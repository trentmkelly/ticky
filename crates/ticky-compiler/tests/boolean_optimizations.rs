//! Boolean cover, guarded-load and physical decider sharing regressions.
use ticky_compiler::testrun::run_tests;
use ticky_compiler::{compile, Opt, Options};
use ticky_factorio::netlist::Kind;

fn check(src: &str) -> ticky_compiler::Compiled {
    let mut result = None;
    for opt in [Opt::Speed, Opt::Size] {
        for checks in [false, true] {
            let c = compile(src, &Options { opt, checks, ..Default::default() }).unwrap_or_else(|d| panic!("{d:?}"));
            assert!(c.cg.netlist.validate(true).is_empty());
            for r in run_tests(&c, src) {
                assert!(r.failure.is_none(), "{}: {:?}", r.name, r.failure);
            }
            if !checks && matches!(opt, Opt::Size) {
                result = Some(c);
            }
        }
    }
    result.unwrap()
}

fn count(c: &ticky_compiler::Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count()
}

const COMPLEMENT: &str = r#"input a: int @ A
input x: int @ X
output y: int @ Y
every 30 ticks:
    y = 7 if ((a > 0 and x*x > 10) or (a > 0 and x*x <= 10)) else 0

test "both predicates and overflow":
    set a = 1
    set x = 4
    run 90 ticks
    assert y == 7
    set x = 2147483647
    run 90 ticks
    assert y == 7
    set a = -1
    run 90 ticks
    assert y == 0
"#;

const EQUAL_LOAD: &str = r#"input a: int @ A
input b: int @ B
output y: int @ Y
every 30 ticks:
    if a > 0:
        y = 7
    elif b > 0:
        y = 7

test "load and hold":
    run 90 ticks
    assert y == 0
    set b = 1
    run 90 ticks
    assert y == 7
    set b = 0
    run 90 ticks
    assert y == 7
    set a = 1
    run 90 ticks
    assert y == 7
"#;

const SHARED_LOGIC: &str = r#"input a: int @ A
input b: int @ B
input c: int @ C
output y: int @ Y
output z: int @ Z
every 30 ticks:
    y = (7 if a > 0 else 3) * b
    z = (9 if a > 0 else 4) * c

test "both coefficient arms":
    set a = 1
    set b = 11
    set c = -5
    run 90 ticks
    assert y == 77 and z == -45
    set a = 0
    run 90 ticks
    assert y == 33 and z == -20
    set b = -2147483648
    set c = 2147483647
    run 90 ticks
    assert y == -2147483648 and z == -4
"#;

#[test]
fn complementary_predicate_drops_dead_arithmetic() {
    let c = check(COMPLEMENT);
    let simpler = COMPLEMENT.replace("((a > 0 and x*x > 10) or (a > 0 and x*x <= 10))", "a > 0");
    assert_eq!(count(&c), count(&check(&simpler)));
}

#[test]
fn equal_loads_merge_and_keep_holding() {
    let c = check(EQUAL_LOAD);
    let simpler = EQUAL_LOAD.replace("if a > 0:\n        y = 7\n    elif b > 0:", "if a > 0 or b > 0:");
    assert_eq!(count(&c), count(&check(&simpler)));
    // Zero-valued leaves must stop a previously nonzero hold.
    check(
        r#"input a: int @ A
input b: int @ B
output y: int @ Y
every 30 ticks:
    if a < 0:
        y = 7
    elif a > 0:
        y = 0
    elif b > 0:
        y = 0

test "zero disables holding":
    set a = -1
    run 90 ticks
    assert y == 7
    set a = 0
    set b = 1
    run 90 ticks
    assert y == 0
    set b = 0
    run 90 ticks
    assert y == 0
    set a = -1
    run 90 ticks
    assert y == 7
    set a = 1
    run 90 ticks
    assert y == 0
"#,
    );
}

#[test]
fn settled_coefficients_share_two_physical_deciders() {
    let c = check(SHARED_LOGIC);
    let shared =
        c.cg.netlist
            .entities
            .iter()
            .filter(|e| e.description.as_deref().is_some_and(|s| s.contains(": condition") || s.contains(": select")) && matches!(&e.kind, Kind::Decider(d) if d.outputs.len() == 2 && d.outputs.iter().all(|o| !o.copy)))
            .count();
    assert_eq!(shared, 2, "each predicate should produce both coefficients");
}

#[test]
fn simplified_condition_preserves_division_check() {
    let src = r#"input a: int @ A
input x: int @ X
output y: int @ Y
every 30 ticks:
    q = 10 // x
    y = 7 if ((a > 0 and q > 10) or (a > 0 and q <= 10)) else 0

test "dead predicate keeps runtime error":
    set a = 1
    run 90 ticks
    assert error != 0
"#;
    for opt in [Opt::Speed, Opt::Size] {
        let c = compile(src, &Options { opt, checks: true, ..Default::default() }).unwrap_or_else(|d| panic!("{d:?}"));
        for r in run_tests(&c, src) {
            assert!(r.failure.is_none(), "{}: {:?}", r.name, r.failure);
        }
    }
}
