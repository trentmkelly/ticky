use ticky_compiler::{compile, testrun::run_tests, Compiled, Opt, Options};

fn build(src: &str, opt: Opt, checks: bool) -> Compiled {
    let c = compile(src, &Options { opt, checks, ..Default::default() })
        .unwrap_or_else(|ds| panic!("{}", ds.iter().map(|d| d.render("results", src)).collect::<String>()));
    assert!(c.cg.netlist.validate(true).is_empty());
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "{}: {:?}", r.name, r.failure);
    }
    c
}

#[test]
fn unused_second_moment_drops_transport_but_keeps_loop_timing() {
    let src = include_str!("../../../examples/production-moments.ticky");
    for opt in [Opt::Size, Opt::Speed] {
        for checks in [false, true] {
            let c = build(src, opt, checks);
            assert!(c.program.subroutines.contains("ramp_moments"));
            let count = c.cg.netlist.entities.iter().filter(|e| e.kind.proto_name().ends_with("combinator")).count();
            assert!(count <= if checks { 42 } else { 40 }, "unused moment still emitted: {count}");
            // Baseline loop body takes four ticks. Dead arithmetic must not advance
            // the next call's sample or the eventual output commit.
            assert!(c.program.procs[0].steps.iter().any(|s| s.depth == 3));
        }
    }
}

#[test]
fn union_of_callers_keeps_each_demanded_tuple_component() {
    let src = r#"input x: int @ X
output y: int @ Y
def moments(n):
    a = 0
    b = 0
    for i in range(3):
        a += n + i
        b += (n + i) * (n + i)
    return a, b
while True:
    a, unused = moments(x)
    unused, b = moments(x + 1)
    y = a + b
    wait 1
test "distinct caller demand":
    set x = 2
    run 300 ticks
    assert y == 59
    set x = -3
    run 300 ticks
    assert y == -1
"#;
    for opt in [Opt::Size, Opt::Speed] {
        for checks in [false, true] { build(src, opt, checks); }
    }
}

#[test]
fn discarded_returns_preserve_effects_waits_and_early_exit() {
    let src = r#"input x: int @ X
output seen: int @ S
output result: int @ R
def report(n):
    global seen
    seen += 1
    wait 4
    if n < 0:
        return n, n * n
    seen += 10
    return n + 1, n * n
while True:
    a, ignored = report(x)
    b, ignored = report(-1)
    result = a + b
    wait 100
test "side effects and early return":
    set x = 7
    run 80 ticks
    assert seen == 12
    assert result == 7
"#;
    for opt in [Opt::Size, Opt::Speed] {
        for checks in [false, true] { build(src, opt, checks); }
    }
}

#[test]
fn unused_checked_result_still_halts() {
    let src = r#"input x: int @ X
output y: int @ Y
def checked(n):
    wait 1
    return n + 1, 100 // n
while True:
    a, ignored = checked(x)
    b, ignored = checked(x + 1)
    y = a + b
    wait 1
test "discarded division check":
    set x = 0
    run 100 ticks
    assert error != 0
    assert y == 0
"#;
    for opt in [Opt::Size, Opt::Speed] { build(src, opt, true); }
}

#[test]
fn tuple_array_results_survive_later_calls_and_copy_on_write() {
    let src = r#"input x: int @ X
input index: int @ I
output y: int @ Y
def samples(n):
    values = [n, n + 1, n + 2, n + 3]
    wait 1
    return n * 2, values
while True:
    a, first = samples(x)
    b, second = samples(x + 10)
    first[index] += 100
    y = a + b + first[index] + second[index]
    wait 1
test "array results are independent":
    set x = 2
    set index = 1
    run 150 ticks
    assert y == 144
    set x = -5
    set index = 3
    run 150 ticks
    assert y == 106
"#;
    for opt in [Opt::Size, Opt::Speed] {
        for checks in [false, true] { build(src, opt, checks); }
    }
}
