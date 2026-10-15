//! Regressions found by translation validation (`tools/validate.py`).
use ticky_compiler::testrun::{Harness, PVal};
use ticky_compiler::{compile, Options};

/// Found as a failed element-range obligation on a `fuzz_elemranges` program: a comprehension
/// condition on a value of `v` that isn't `v` itself (`t + 7 > -40` inside `min(t + 7, -40)`)
/// is lowered as "the difference with 0 on every signal" (bundle.rs `Conv::restrict`:
/// `(t + 7) - (-40) > 0`, i.e. `t + 47 > 0`), which is wrong when the difference wraps even
/// though nothing in the source overflows: with `t = 2147483620`, `t + 7 = 2147483627` and
/// `min(...)` is -40, but `t + 47` wraps negative and the element comes out as `t + 7`.
#[test]
#[ignore = "known bug in comprehension conditions (bundle.rs Conv::restrict), not fixed yet"]
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
