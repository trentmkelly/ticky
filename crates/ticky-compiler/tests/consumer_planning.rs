use ticky_compiler::{compile, testrun::run_tests, Opt, Options};

fn verify(src: &str, options: &Options) -> usize {
    let c = compile(src, options).unwrap_or_else(|d| panic!("{}", d[0].render("consumer", src)));
    assert!(c.cg.netlist.validate(true).is_empty());
    for test in run_tests(&c, src) {
        if let Some(d) = test.failure { panic!("{}", d.render("consumer", src)); }
    }
    c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count()
}

fn source(expression: &str, eval: fn(i32, i32) -> i32, reduction: &str, binding: bool) -> String {
    let producer = format!("[{expression} for k in range(1,17)]");
    let body = if binding { format!("    xs = {producer}\n    y = {reduction}(xs)") } else { format!("    y = {reduction}({producer})") };
    let mut src = format!("input x: int @ X\noutput y: int @ Y\nevery 60 ticks:\n{body}\ntest \"values\":\n");
    for x in [0, 1, -3, i32::MIN, i32::MAX] {
        let xs: Vec<i32> = (1..17).map(|k| eval(k, x)).collect();
        let y = match reduction {
            "sum" => xs.into_iter().fold(0i32, i32::wrapping_add),
            "min" => *xs.iter().min().unwrap(),
            "max" => *xs.iter().max().unwrap(),
            _ => unreachable!(),
        };
        src.push_str(&format!("    set x = {x}\n    run 180 ticks\n    assert y == {y}\n"));
    }
    src
}

#[test]
fn whole_reductions_preserve_wrapping_floor_division_and_zero_slots() {
    let cases: [(&str, fn(i32, i32) -> i32); 6] = [
        ("min(k,x)", |k, x| k.min(x)),
        ("min(k*x,20)", |k, x| k.wrapping_mul(x).min(20)),
        ("k < x", |k, x| (k < x) as i32),
        ("(k*x)//-7", |k, x| { let a = k.wrapping_mul(x); a / -7 - i32::from(a % -7 > 0) }),
        ("(k*x)%7", |k, x| k.wrapping_mul(x).rem_euclid(7)),
        ("k*x if k<x else 0", |k, x| if k < x { k.wrapping_mul(x) } else { 0 }),
    ];
    for (expression, eval) in cases {
        for reduction in ["sum", "min", "max"] {
            for binding in [false, true] {
                let src = source(expression, eval, reduction, binding);
                for opt in [Opt::Speed, Opt::Size] {
                    for checks in [false, true] {
                        verify(&src, &Options { opt, checks, ..Default::default() });
                    }
                }
            }
        }
    }
}

#[test]
fn adjacent_reduction_eliminates_unneeded_scalar_array_producers() {
    let src = source("min(k,x)", |k, x| k.min(x), "sum", true);
    assert!(verify(&src, &Options::default()) <= 15, "59 combinators before consumer planning");
    let direct = source("k*x+1", |k, x| k.wrapping_mul(x).wrapping_add(1), "min", false);
    assert!(verify(&direct, &Options::default()) <= 16, "117 combinators before consumer planning");
    verify(&src.replace("every 60 ticks:", "every tick:"), &Options::default());
}

#[test]
fn array_snapshots_and_other_consumers_stay_intact() {
    let src = r#"input x: int @ X
output y: int @ Y
output z: int @ Z
every 60 ticks:
    local = x
    xs = [min(k,local) for k in range(16)]
    local = -100
    y = sum(xs)
    z = xs[7]
test "snapshot":
    set x = 3
    run 180 ticks
    assert y == 42 and z == 3
    set x = -3
    run 180 ticks
    assert y == -48 and z == -3
"#;
    verify(src, &Options { checks: true, ..Default::default() });
    // Boolean reductions can collapse to one scalar predicate later in compilation;
    // selecting their bundle form from IR operation counts would make these larger.
    let boolean = "input x: int @ X\noutput y: bool @ Y\nevery 60 ticks:\n    y = any([min(k,x) for k in range(16)])\n";
    assert!(verify(boolean, &Options::default()) <= 11);
}

#[test]
fn ordered_computed_comparisons_fall_back_before_subtraction_wraps() {
    let src = "input x: int @ X\noutput y: int @ Y\nevery 60 ticks:\n    y = sum([min(k,x) for k in range(16)])\ntest \"extreme comparison\":\n    set x = -2147483648\n    run 180 ticks\n    assert y == 0\n    set x = 2147483647\n    run 180 ticks\n    assert y == 120\n";
    verify(src, &Options { checks: true, ..Default::default() });
}

#[test]
fn multi_bank_total_and_runtime_checks_are_preserved() {
    let n = ticky_compiler::expand::bank_size() + 3;
    let expected = (0..n as i32).map(|k| k.wrapping_mul(-3)).fold(0i32, i32::wrapping_add);
    let src = format!("input x: int @ X\noutput y: int @ Y\nevery 60 ticks:\n    y = sum([k*x for k in range({n})])\ntest \"banks\":\n    set x = -3\n    run 180 ticks\n    assert y == {expected}\n    set x = 0\n    run 180 ticks\n    assert y == 0\n");
    verify(&src, &Options { checks: true, ..Default::default() });
    // A nonconstant floor divisor has no vector alternative: its original runtime
    // checks must remain, including the failure after previously successful inputs.
    let checked = "input x: int @ X\noutput y: int @ Y\nevery 60 ticks:\n    y = sum([k//x for k in range(1,17)])\ntest \"division check\":\n    set x = 1\n    run 180 ticks\n    assert y == 136 and error == 0\n    set x = 0\n    run 180 ticks\n    assert error != 0\n";
    verify(checked, &Options { checks: true, ..Default::default() });
}
