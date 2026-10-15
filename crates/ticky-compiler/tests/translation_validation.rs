//! Regressions found by translation validation (`tools/validate.py`).
use ticky_compiler::testrun::{Harness, PVal};
use ticky_compiler::{compile, Options};

fn settle(src: &str, inputs: &[(&str, i32)], output: &str) -> Vec<PVal> {
    let mut out = Vec::new();
    for checks in [false, true] {
        let c = compile(src, &Options { checks, ..Default::default() }).unwrap();
        let mut h = Harness::new(&c);
        for (n, v) in inputs {
            h.set(c.program.port_index(n).unwrap(), PVal::Int(*v));
        }
        for _ in 0..40 {
            h.sim.step();
        }
        out.push(h.get(c.program.port_index(output).unwrap()));
    }
    out
}

/// Found as a failed element-range obligation on examples/dashboard.ticky (digit drawing
/// divides a temperature input by a table of digit weights); minimised, a failed `cmp` claim. The interval of
/// a truncating division by a non-constant left out MIN (`MIN / 1` is MIN), so comparing the
/// quotient with MIN folded to a constant (ir.rs `ar_interval`, fixed).
#[test]
fn quotient_interval_includes_min() {
    let src = "input x: int @ X\ninput y: int @ Y\noutput o: bool @ A\noutput p: int @ B\nevery tick:\n    o = tdiv(x, y) == -2147483648\n    p = 1 if tdiv(x, y) < -2147483647 else 2\n";
    let min = i32::MIN;
    assert_eq!(settle(src, &[("x", min), ("y", 1)], "o"), vec![PVal::Int(1); 2]);
    assert_eq!(settle(src, &[("x", min), ("y", 1)], "p"), vec![PVal::Int(1); 2]);
    assert_eq!(settle(src, &[("x", min), ("y", -1)], "o"), vec![PVal::Int(0); 2]);
    assert_eq!(settle(src, &[("x", 7), ("y", 2)], "p"), vec![PVal::Int(2); 2]);
}

/// Found as a failed element-range obligation on a `fuzz_elemranges` program: a comprehension
/// condition on a value of `v` that isn't `v` itself (`t + 7 > -40` inside `min(t + 7, -40)`)
/// is lowered as "the difference with 0 on every signal" (bundle.rs `Conv::restrict`:
/// `(t + 7) - (-40) > 0`, i.e. `t + 47 > 0`), which is wrong when the difference wraps even
/// though nothing in the source overflows: with `t = 2147483620`, `t + 7 = 2147483627` and
/// `min(...)` is -40, but `t + 47` wraps negative and the element came out as `t + 7`. Fixed
/// for conditions with a constant side (compared directly); the difference remains for
/// other conditions (`v` on both sides, or a runtime scalar: domain filters need constants).
#[test]
fn comprehension_condition_with_a_runtime_scalar_compiles() {
    // Domain filters compare with constants only: a first version of the fix above compared
    // `v // x` with `x` directly and codegen panicked (a fuzz_bundles program).
    let src = "input a: Bundle\ninput b: Bundle\ninput x: int @ X\noutput o: Bundle\noutput t: int @ T\nwhile True:\n    o = {s: max((v // x), x) for s, v in (b + b).items() if v != x}\n    t = len(o) * 1000 + o.total()\n    wait 3\n";
    for checks in [false, true] {
        compile(src, &Options { checks, ..Default::default() }).unwrap();
    }
}

#[test]
fn comprehension_condition_difference_must_not_wrap() {
    let src = "input x: int @ X\ninput i: int @ I\noutput o: int @ A\nxs = [0, 0]\nevery tick:\n    xs[i] = x\n    ys = [min(t + 7, -40) for t in xs]\n    o = ys[i]\n";
    for checks in [false, true] {
        let c = compile(src, &Options { checks, ..Default::default() }).unwrap();
        let mut h = Harness::new(&c);
        let port = |n| c.program.port_index(n).unwrap();
        for x in [5, 2147483620, i32::MAX - 40, i32::MAX - 8] {
            h.set(port("x"), PVal::Int(x));
            h.set(port("i"), PVal::Int(0));
            for _ in 0..40 {
                h.sim.step();
            }
            let want = (x as i64 + 7).min(-40) as i32;
            assert_eq!(h.get(port("o")), PVal::Int(want), "x = {x}, checks {checks}");
        }
    }
}
