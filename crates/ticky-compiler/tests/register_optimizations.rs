use ticky_compiler::{compile, testrun::run_tests, Compiled, Options};

fn checked(src: &str) -> Compiled {
    let c = compile(src, &Options { checks: true, ..Default::default() })
        .unwrap_or_else(|ds| panic!("{}", ds.iter().map(|d| d.render("probe", src)).collect::<String>()));
    assert!(c.cg.netlist.validate(true).is_empty());
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "{}: {:?}", r.name, r.failure);
    }
    c
}

#[test]
fn overwritten_store_keeps_duration_and_checks() {
    let src = r#"input a: int @ A
input b: int @ B
output out: int @ O
wait 1
x = (a * 7 + b) * 3
wait 1
x = b
wait 1
out = x

test "last store":
    set a = 4
    set b = 9
    run 40 ticks
    assert out == 9
"#;
    let c = checked(src);
    let m = &c.program.procs[0];
    let x = c.program.states.iter().position(|s| s.name == "x").unwrap();
    let removed: Vec<_> = m.steps.iter().filter(|s| s.writes.iter().any(|(si, _)| *si == x)
        && !s.plans.iter().any(|(si, _)| *si == x)).collect();
    assert!(!removed.is_empty());
    assert!(removed.iter().any(|s| s.depth >= 2), "dead arithmetic must retain its original depth");
    assert!(!c.cg.netlist.entities.iter().any(|e| e.description.as_deref().is_some_and(|d| d.contains("input `a` (load)"))));

    let checked_dead = r#"input a: int @ A
output out: int @ O
wait 1
x = 100 // a
wait 1
x = 7
wait 1
out = x

test "dead checked division still fails":
    set a = 0
    run 30 ticks
    assert error != 0
"#;
    checked(checked_dead);
}

#[test]
fn observable_stores_and_assignment_errors_remain() {
    let src = r#"input a: int @ A
output out: int @ O
output observed: int @ V
x = 0
every tick:
    observed = x
wait 1
x = a + 7
wait 20
x = 3
wait 20
out = x

test "foreign reader sees intermediate value":
    set a = 4
    run 15 ticks
    assert observed == 11
    run 60 ticks
    assert observed == 3 and out == 3
"#;
    checked(src);
    let bad = "output o: int\nwait 1\nx = y\nwait 1\nx = 3\ny = 4\nwait 1\no = x\n";
    assert!(compile(bad, &Options::default()).is_err());
}

#[test]
fn whole_bundle_lifetimes_share_storage() {
    let src = r#"input a: Bundle
output first: int @ F
output second: int @ S
output done: bool @ D
wait 1
left = a + Bundle(iron_plate=1)
wait 1
first = left.iron_plate
wait 1
right = a + Bundle(copper_plate=2)
wait 1
second = right.copper_plate
done = True

test "separate bundle lifetimes":
    set a = Bundle(iron_plate=5, copper_plate=9)
    run until done, max 80 ticks
    assert first == 6 and second == 11
"#;
    let c = checked(src);
    assert!(c.program.states.iter().any(|s| s.name == "left" && s.shared.iter().any(|n| n == "right")));
    let holds: Vec<_> = c.cg.netlist.entities.iter().filter_map(|e| e.description.as_deref())
        .filter(|d| d.contains("`left` / `right`") && d.ends_with("(hold)")).collect();
    assert_eq!(holds.len(), 1);
}

#[test]
fn accumulator_bank_shares_holds_and_resets() {
    let src = r#"input a: int @ A
input b: int @ B
input reset: bool @ R
output x: int @ X
output y: int @ Y
x = 5
y = 10
every tick:
    if reset:
        x = 5
        y = 10
    else:
        x += a
        y += b

test "independent accumulation and reset":
    set a = 2
    set b = 4
    run 30 ticks
    assert x > 5 and y == 2 * x
    set reset = True
    run 15 ticks
    assert x == 5 and y == 10
    set a = -3
    set b = -6
    set reset = False
    run 25 ticks
    assert x < 5 and y == 2 * x
"#;
    let c = checked(src);
    for suffix in ["(accumulator)", "(hold while starting)"] {
        let es: Vec<_> = c.cg.netlist.entities.iter().filter_map(|e| e.description.as_deref())
            .filter(|d| d.contains(suffix)).collect();
        assert_eq!(es.len(), 1, "{suffix}: {es:?}");
        assert!(es[0].contains("`x`") && es[0].contains("`y`"));
    }
}

#[test]
fn coloring_avoids_alphabetical_three_color_path() {
    // Interference path a--c--d--b: name-order first-fit uses three registers,
    // degree order uses {a,d} and {b,c}. Every edge is exercised in its own phase.
    let src = r#"input input_value: int @ I
output out: int @ O
output done: bool @ D
wait 1
a = input_value
c = input_value + 1
wait 1
out = a + c
wait 1
c = input_value + 2
d = input_value + 3
wait 1
out = c + d
wait 1
b = input_value + 4
d = input_value + 5
wait 1
out = b + d
done = True

test "two-register path":
    set input_value = 10
    run until done, max 100 ticks
    assert out == 29
"#;
    let c = checked(src);
    for (rep, member) in [("a", "d"), ("b", "c")] {
        assert!(c.program.states.iter().any(|s| s.name == rep && s.shared.iter().any(|n| n == member)));
    }
}

#[test]
fn unobserved_state_cycle_does_not_keep_registers_alive() {
    let src = r#"input input_value: int @ I
output out: int @ O
a = 0
b = 0
wait 1
while True:
    a = b + input_value
    wait 1
    b = a + input_value
    wait 1
    out += 1

test "dead state cycle":
    set input_value = 17
    run 50 ticks
    assert out > 0
"#;
    let c = checked(src);
    for s in &c.program.procs[0].steps {
        assert!(s.plans.iter().all(|(si, _)| c.program.states[*si].name == "out"));
    }
    assert!(c.program.procs[0].used_sources().iter().all(|&i|
        !matches!(c.program.procs[0].srcs[i], ticky_compiler::program::SrcKind::Input(_))));
}

#[test]
fn accumulator_bank_keeps_different_reset_guards_independent() {
    let src = r#"input reset_x: bool @ A
input reset_y: bool @ B
output x: int @ X
output y: int @ Y
every tick:
    if reset_x:
        x = 0
    else:
        x += 2
    if reset_y:
        y = 7
    else:
        y += 3

test "separate resets on shared feedback":
    set reset_x = True
    run 30 ticks
    assert x == 0 and y > 7
    set reset_x = False
    set reset_y = True
    run 30 ticks
    assert x > 0 and y == 7
"#;
    checked(src);
}
