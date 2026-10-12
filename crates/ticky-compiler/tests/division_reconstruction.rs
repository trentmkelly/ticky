//! Signed quotient/remainder reconstruction, including Factorio's exceptional division.
use ticky_compiler::{compile, Compiled, Opt, Options};
use ticky_compiler::testrun::{run_tests, Harness, PVal};

fn get(h: &Harness<'_>, name: &str) -> i32 {
    let PVal::Int(v) = h.get(h.c.program.port_index(name).unwrap()) else { panic!() };
    v
}
fn set(h: &mut Harness<'_>, name: &str, v: i32) {
    h.set(h.c.program.port_index(name).unwrap(), PVal::Int(v));
}
fn count(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count()
}
fn source(divisor: &str) -> String {
    format!("input x: int @ X\ninput y: int @ Y\noutput q: int @ Q\noutput r: int @ R\nevery tick:\n    d = {divisor}\n    q = tdiv(x, d)\n    r = x - tdiv(x, d) * d\n")
}
fn expected(x: i32, d: i32) -> (i32, i32) {
    let q = x.checked_div(d).unwrap_or(0);
    (q, x.wrapping_sub(q.wrapping_mul(d)))
}

#[test]
fn duration_example_counts_and_tests() {
    let src = include_str!("../../../examples/signed-duration.ticky");
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] {
            let c = compile(src, &Options { opt, checks, ..Default::default() }).unwrap();
            // Frozen baseline: 11 without checks, 13 with checks, for either objective.
            assert_eq!(count(&c), if checks { 9 } else { 7 }, "{opt:?}, checks={checks}: {}", count(&c));
            for result in run_tests(&c, src) {
                assert!(result.failure.is_none(), "{}: {:?}", result.name, result.failure);
            }
        }
    }
}

#[test]
fn proven_nonzero_divisors_match_native_remainder_cost() {
    for divisor in ["3600", "-3600", "clamp(y, 2, 10000)", "clamp(y, -10000, -2)", "-2147483648"] {
        for swapped in [false, true] {
            let mut src = source(divisor);
            if swapped { src = src.replace("tdiv(x, d) * d", "d * tdiv(x, d)"); }
            let reduced = source(divisor).replace("x - tdiv(x, d) * d", "tmod(x, d)");
            for opt in [Opt::Speed, Opt::Size] {
                let opts = Options { opt, ..Default::default() };
                assert_eq!(count(&compile(&src, &opts).unwrap()), count(&compile(&reduced, &opts).unwrap()), "{divisor}, swapped={swapped}, {opt:?}");
            }
        }
    }
}

#[test]
fn signed_reconstruction_streaming_extremes_and_exceptions() {
    let values = [i32::MIN, i32::MAX, -1, 0, 1, 3600, -3601, 123456789, -987654321];
    let divisors: &[(&str, fn(i32) -> i32)] = &[
        ("3600", |_| 3600), ("-3600", |_| -3600),
        ("clamp(y, 2, 10000)", |y| y.clamp(2, 10000)),
        ("clamp(y, -10000, -2)", |y| y.clamp(-10000, -2)),
        ("y", |y| y), ("0", |_| 0), ("-1", |_| -1),
        ("-2147483648", |_| i32::MIN),
    ];
    for checks in [false, true] {
        for &(expr, divisor) in divisors {
            let c = compile(&source(expr), &Options { checks, ..Default::default() }).unwrap();
            let mut h = Harness::new(&c);
            let inputs = |t: usize| (values[t % values.len()], values[(t / values.len()) % values.len()]);
            let observed: Vec<_> = (0..180).map(|t| {
                let (x, y) = inputs(t);
                set(&mut h, "x", x);
                set(&mut h, "y", y);
                h.sim.step();
                (get(&h, "q"), get(&h, "r"))
            }).collect();
            assert!((0..25).any(|lag| (40..180).all(|t| {
                let (x,y) = inputs(t-lag);
                observed[t] == expected(x, divisor(y))
            })), "unaligned values for {expr}, checks={checks}");
        }
    }
}

#[test]
fn reconstruction_wrapping_input_and_restart() {
    let src = source("3600").replace("tdiv(x, d)", "tdiv(x + y, d)").replace("r = x -", "r = (x + y) -");
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] {
            let c = compile(&src, &Options { opt, checks, ..Default::default() }).unwrap();
            let mut h = Harness::new(&c);
            for (x, y) in [(i32::MAX, 1), (i32::MIN, -1), (-3601, 0)] {
                set(&mut h, "x", x); set(&mut h, "y", y);
                for _ in 0..60 { h.sim.step(); }
                assert_eq!((get(&h, "q"), get(&h, "r")), expected(x.wrapping_add(y), 3600));
                h.sim.set_constant_on(c.cg.run_switch, false);
                for _ in 0..30 { h.sim.step(); }
                h.sim.set_constant_on(c.cg.run_switch, true);
                for _ in 0..60 { h.sim.step(); }
                assert_eq!((get(&h, "q"), get(&h, "r")), expected(x.wrapping_add(y), 3600));
            }
        }
    }
}

#[test]
fn floor_division_check_is_retained() {
    let src = "input x: int @ X\ninput y: int @ Y\noutput r: int @ R\nevery tick:\n    r = x - (x // y) * y\n";
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] {
            let c = compile(src, &Options { opt, checks, ..Default::default() }).unwrap();
            let mut h = Harness::new(&c);
            set(&mut h, "x", 17); set(&mut h, "y", 0);
            for _ in 0..80 { h.sim.step(); }
            if checks { assert_ne!(get(&h, "error"), 0); }
            else { assert_eq!(get(&h, "r"), 17); }
        }
    }
}
