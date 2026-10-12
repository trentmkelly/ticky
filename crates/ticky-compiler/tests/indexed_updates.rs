use ticky_compiler::{compile, testrun::{run_tests, Harness, PVal}, Compiled, Opt, Options};

fn build(src: &str, opt: Opt, checks: bool) -> Compiled {
    let c = compile(src, &Options { opt, checks, ..Default::default() }).unwrap();
    assert!(c.cg.netlist.validate(true).is_empty());
    for result in run_tests(&c, src) {
        assert!(result.failure.is_none(), "{}: {:?}", result.name, result.failure);
    }
    c
}
fn count(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count()
}
fn set(h: &mut Harness<'_>, name: &str, x: i32) {
    h.set(h.c.program.port_index(name).unwrap(), PVal::Int(x));
}
fn value(h: &Harness<'_>, name: &str) -> i32 {
    let PVal::Int(x) = h.get(h.c.program.port_index(name).unwrap()) else { panic!() };
    x
}
fn ticks(h: &mut Harness<'_>, n: usize) { for _ in 0..n { h.sim.step(); } }

#[test]
fn saved_read_update_has_augmented_assignment_cost() {
    let src = include_str!("../../../examples/bin_ledger.ticky");
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] {
            let c = build(src, opt, checks);
            let augmented = build(&src.replace("bins[pick] = previous + amount", "bins[pick] += amount"), opt, checks);
            assert_eq!(count(&c), count(&augmented));
            // Commuted sums and subtraction share the same sparse-update identity.
            build(&src.replace("previous + amount", "amount + previous"), opt, checks);
            build(&src.replace("previous + amount", "previous - (-amount)"), opt, checks);
        }
    }
}

#[test]
fn older_snapshots_other_indices_and_other_arrays_do_not_match() {
    let src = r#"input i: int @ I
input j: int @ J
input x: int @ X
output a: int @ A
output b: int @ B
output c: int @ C
xs = [0] * 64
ys = [0] * 64
wait 10
xs[i] = x
old = xs[i]
xs[i] = 3
xs[i] = old + 2
ys[i] = xs[i] + 4
xs[j] = xs[i] + 7
a = xs[i]
b = xs[j]
c = ys[i]
test "saved values are snapshots":
    set i = 7
    set j = 9
    set x = 20
    run 100 ticks
    assert a == 22 and b == 29 and c == 26
"#;
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] { build(src, opt, checks); }
    }
}

#[test]
fn invalid_indices_still_check_and_unchecked_writes_are_noops() {
    let src = "input i: int @ I\ninput x: int @ X\noutput total: int @ T\nxs = [0] * 64\nwait 10\nxs[i] = xs[i] + x\ntotal = sum(xs)\n";
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] {
            let c = build(src, opt, checks);
            for i in [-2147483648, -1, 64, 2147483647] {
                let mut h = Harness::new(&c);
                set(&mut h, "i", i);
                set(&mut h, "x", 2147483647);
                ticks(&mut h, 100);
                assert_eq!(value(&h, "total"), 0);
                if checks { assert_ne!(value(&h, "error"), 0); }
            }
        }
    }
}

#[test]
fn input_sampling_and_restart_preserve_the_ledger() {
    let src = include_str!("../../../examples/bin_ledger.ticky");
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] {
            let c = build(src, opt, checks);
            let mut h = Harness::new(&c);
            set(&mut h, "pick", 5);
            set(&mut h, "amount", 17);
            set(&mut h, "strobe", 1);
            ticks(&mut h, 80);
            assert_eq!(value(&h, "stock"), 17);
            h.sim.set_constant_on(c.cg.run_switch, false);
            set(&mut h, "strobe", 0);
            ticks(&mut h, 40);
            h.sim.set_constant_on(c.cg.run_switch, true);
            ticks(&mut h, 40);
            assert_eq!(value(&h, "stock"), 0);
            set(&mut h, "pick", 63);
            set(&mut h, "amount", -23);
            set(&mut h, "strobe", 1);
            ticks(&mut h, 80);
            assert_eq!(value(&h, "stock"), -23);
            assert_eq!(value(&h, "before"), 0);
        }
    }
}

#[test]
fn banked_arrays_keep_global_indices_and_sparse_zeroes() {
    let src = r#"input i: int @ I
input x: int @ X
input go: bool @ G
output selected: int @ S
output total: int @ T
xs = [0] * 400
while True:
    wait until go
    previous = xs[i]
    xs[i] = previous + x
    selected = xs[i]
    total = sum(xs)
    wait until not go

test "updates cross the bank boundary":
    set i = 378
    set x = -2147483648
    set go = True
    run 100 ticks
    assert selected == -2147483648 and total == -2147483648
    set go = False
    run 40 ticks
    set i = 7
    set x = 15
    set go = True
    run 100 ticks
    assert selected == 15 and total == -2147483633
    set go = False
    run 40 ticks
    set i = 378
    set x = -2147483648
    set go = True
    run 100 ticks
    assert selected == 0 and total == 15
"#;
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] { build(src, opt, checks); }
    }
}

#[test]
fn changing_inputs_match_augmented_update_tick_for_tick() {
    let src = include_str!("../../../examples/bin_ledger.ticky");
    let augmented = src.replace("bins[pick] = previous + amount", "bins[pick] += amount");
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] {
            let a = build(src, opt, checks);
            let b = build(&augmented, opt, checks);
            let (mut ha, mut hb) = (Harness::new(&a), Harness::new(&b));
            let mut changed = false;
            for tick in 0..300i32 {
                for h in [&mut ha, &mut hb] {
                    set(h, "pick", (tick / 3) % 64);
                    set(h, "amount", tick.wrapping_mul(123456789));
                    set(h, "strobe", i32::from(tick % 30 < 15));
                    ticks(h, 1);
                }
                for output in ["before", "after", "stock", "total"] {
                    assert_eq!(value(&ha, output), value(&hb, output), "tick {tick}, {output}");
                }
                changed |= value(&ha, "total") != 0;
            }
            assert!(changed, "changing input stream must actually write the ledger");
        }
    }
}
