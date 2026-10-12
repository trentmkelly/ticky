//! Semantic and combinator regressions for weighted counts and lookup encodings.
use ticky_compiler::{compile, testrun::run_tests, Opt, Options};
use ticky_factorio::CmpOp;

fn verify(src: &str, checks: bool) -> ticky_compiler::Compiled {
    let mut compiled = None;
    for opt in [Opt::Speed, Opt::Size] {
        let c = compile(src, &Options { checks, opt, ..Default::default() }).unwrap_or_else(|d| panic!("{}", d[0].message));
        assert!(c.cg.netlist.validate(true).is_empty());
        for r in run_tests(&c, src) {
            if let Some(d) = r.failure {
                panic!("{}: {}", r.name, d.message);
            }
        }
        compiled = Some(c);
    }
    compiled.unwrap()
}

fn made(c: &ticky_compiler::Compiled, what: &str) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.description.as_deref().is_some_and(|d| d.ends_with(what))).count()
}

#[test]
fn counted_comparisons_keep_missing_slots_and_ignore_foreign_signals() {
    for (op, text, reversed) in [
        (CmpOp::Eq, "==", "=="), (CmpOp::Ne, "!=", "!="),
        (CmpOp::Lt, "<", ">"), (CmpOp::Le, "<=", ">="),
        (CmpOp::Gt, ">", "<"), (CmpOp::Ge, ">=", "<="),
    ] {
        let mut src = format!(r#"input b: Bundle
output n: int @ N
every 10 ticks:
    n = (b["coal"] {text} 0) + (0 {reversed} b["stone"]) + (b["wood"] {text} 0) + (b["iron-plate"] {text} 0)
"#);
        for (i, vals) in [[0, 0, 0, 0], [-1, 0, 1, 0], [i32::MIN, i32::MAX, 0, -7]].iter().enumerate() {
            let expected: i32 = vals.iter().map(|x| op.apply(*x, 0) as i32).sum();
            src.push_str(&format!(r#"
test "case {i}":
    set b = {{"coal": {}, "stone": {}, "wood": {}, "iron-plate": {}, "copper-plate": 42}}
    run 40 ticks
    assert n == {expected}
"#, vals[0], vals[1], vals[2], vals[3]));
        }
        for checks in [false, true] {
            let c = verify(&src, checks);
            assert_eq!(made(&c, "filter and total"), 1, "{text}: fused comparison count");
            assert_eq!(made(&c, "read one signal"), 0, "{text}: no per-slot reads");
        }
    }
}

#[test]
fn weighted_counts_wrap_and_combine_repeated_slots() {
    let fixtures = [
        ("2 * (b[\"coal\"] == 7) + 5 * (b[\"stone\"] == 7) - 3 * (b[\"wood\"] == 7)", [2, 5, -3]),
        ("(b[\"coal\"] == 7) + (b[\"coal\"] == 7) + 5 * (b[\"stone\"] == 7) - 3 * (b[\"wood\"] == 7)", [2, 5, -3]),
        ("2147483647 * (b[\"coal\"] == 7) + (b[\"coal\"] == 7) + 2147483647 * (b[\"stone\"] == 7) - 3 * (b[\"wood\"] == 7)", [i32::MIN, i32::MAX, -3]),
        ("-2147483648 * (b[\"coal\"] == 7) - 2147483647 * (b[\"coal\"] == 7) - (b[\"coal\"] == 7) + 5 * (b[\"stone\"] == 7) - 3 * (b[\"wood\"] == 7)", [0, 5, -3]),
    ];
    for (expr, weights) in fixtures {
        let mut src = format!("input b: Bundle\ninput x: int @ X\noutput n: int @ N\nevery 10 ticks:\n    n = {expr} - x\n");
        for mask in 0..8 {
            let values: Vec<i32> = (0..3).map(|i| if mask & (1 << i) != 0 { 7 } else { 0 }).collect();
            let expected = weights.iter().zip(&values).filter(|(_, v)| **v == 7).fold(-13i32, |acc, (w, _)| acc.wrapping_add(*w));
            src.push_str(&format!(r#"
test "mask {mask}":
    set b = {{"coal": {}, "stone": {}, "wood": {}, "iron-plate": 7}}
    set x = 13
    run 40 ticks
    assert n == {expected}
"#, values[0], values[1], values[2]));
        }
        let c = verify(&src, false);
        assert_eq!(made(&c, "filter and total"), 1, "one weighted reduction: {expr}");
        assert_eq!(made(&c, "read one signal"), 0, "no per-slot reads: {expr}");
    }
}


#[test]
fn weighted_zero_tests_include_missing_slots_and_cancelled_weights() {
    let src = r#"input b: Bundle
output n: int @ N
output z: int @ Z
every 10 ticks:
    n = 2 * (b["coal"] == 0) - 3 * (b["stone"] == 0) + 5 * (b["wood"] == 0)
    z = -2147483648 * (b["coal"] == 0) - 2147483647 * (b["coal"] == 0) - (b["coal"] == 0)

test "empty and nonempty":
    set b = {"iron-plate": 7}
    run 40 ticks
    assert n == 4 and z == 0
    set b = {"coal": 5, "wood": -2147483648, "iron-plate": 7}
    run 40 ticks
    assert n == -3 and z == 0
"#;
    let c = verify(src, true);
    assert_eq!(made(&c, "filter and total"), 1, "cancelled weights need no reduction");
    assert_eq!(made(&c, "read one signal"), 0);
}
