use ticky_compiler::{compile, testrun::run_tests, Options};

fn checked(src: &str) -> ticky_compiler::Compiled {
    let c = compile(src, &Options::default()).unwrap_or_else(|d| panic!("{}", d[0].render("probe", src)));
    assert!(c.cg.netlist.validate(true).is_empty());
    for test in run_tests(&c, src) {
        if let Some(d) = test.failure { panic!("{}", d.render("probe", src)); }
    }
    // The same algebra must also preserve sparse semantics in the pipelined emitter.
    let pipelined = src.replace("every 60 ticks:", "every tick:");
    if pipelined != src {
        let p = compile(&pipelined, &Options::default()).unwrap_or_else(|d| panic!("{}", d[0].render("pipeline", &pipelined)));
        assert!(p.cg.netlist.validate(true).is_empty());
        for test in run_tests(&p, &pipelined) {
            if let Some(d) = test.failure { panic!("{}", d.render("pipeline", &pipelined)); }
        }
    }
    c
}

fn made(c: &ticky_compiler::Compiled, suffix: &str) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.description.as_deref().is_some_and(|d| d.ends_with(suffix))).count()
}

#[test]
fn arithmetic_total_fusion_preserves_sparse_wrapping_values() {
    for (expression, expected) in [("a * k", 2147483636i32), ("100 // a", -33), ("a ^ b", -2147483648)] {
        let src = format!(r#"input a: Bundle
input b: Bundle
input k: int @ K
output y: int @ Y
every 60 ticks:
    y = ({expression}).total()
test "values":
    set a = {{"coal": 2147483647, "stone": -3}}
    set b = {{"coal": 7, "wood": 11}}
    set k = 3
    run 180 ticks
    assert y == {expected}
    set a = {{}}
    set b = {{}}
    run 180 ticks
    assert y == 0
"#);
        let c = checked(&src);
        assert_eq!(made(&c, "arithmetic and total"), 1, "{expression}");
        assert_eq!(made(&c, "each with a number") + made(&c, "number with each") + made(&c, "signal by signal"), 0);
    }
}

#[test]
fn shared_maps_are_not_eliminated_by_total_fusion() {
    let c = checked(r#"input a: Bundle
output b: Bundle
output y: int @ Y
every 60 ticks:
    b = a * 3
    y = b.total()
test "shared":
    set a = {"coal": 5, "stone": -7}
    run 180 ticks
    assert b == {"coal": 15, "stone": -21} and y == -6
"#);
    assert_eq!(made(&c, "arithmetic and total"), 0);
}

#[test]
fn sparse_map_algebra_preserves_zero_and_overflow() {
    let c = checked(r#"input a: Bundle
output b: Bundle
output c: Bundle
output d: Bundle
output e: Bundle
every 60 ticks:
    b = (a * 1073741824) * 4
    c = (a & 15) & 7
    d = a * 3 + a * 5
    e = (a + 1) + 2
test "values":
    set a = {"coal": 2147483647, "stone": -1, "wood": 8}
    run 180 ticks
    assert b == {}
    assert c == {"coal": 7, "stone": 7}
    assert d == {"coal": -8, "stone": -8, "wood": 64}
    assert e == {"coal": -2147483646, "wood": 11}
    set a = {}
    run 180 ticks
    assert b == {} and c == {} and d == {} and e == {}
"#);
    assert_eq!(made(&c, "each with a number"), 4, "one mask, one multiply, two sparse additions");
}

#[test]
fn nonzero_comprehension_intermediate_needs_no_second_domain_broadcast() {
    let c = checked(r#"input a: Bundle
input k: int @ K
output b: Bundle
every 60 ticks:
    b = {s: ((v % 10) + 11) | k for s, v in a.items()}
test "zero intermediates and missing lanes":
    set a = {"coal": 10, "stone": -3, "wood": 2147483647}
    set k = 32
    run 180 ticks
    assert b == {"coal": 43, "stone": 40, "wood": 50}
    set k = 0
    run 180 ticks
    assert b == {"coal": 11, "stone": 8, "wood": 18}
    set a = {}
    run 180 ticks
    assert b == {}
"#);
    assert_eq!(made(&c, "filter"), 1, "only the possibly-zero remainder needs domain restoration");
    assert_eq!(made(&c, "each with a number"), 2, "remainder and final OR");
    assert_eq!(made(&c, "signal by signal"), 1, "restoring +11");
}
