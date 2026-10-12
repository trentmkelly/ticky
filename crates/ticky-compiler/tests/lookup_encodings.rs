//! Semantic and combinator regressions for lookup encodings.
use ticky_compiler::{compile, testrun::run_tests, Opt, Options};

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
fn lookup_translation_handles_signed_extremes_and_zero() {
    let mut src = String::from(r#"input x: int @ X
output r: Signal
every 10 ticks:
    r = S("coal") if x == 0 else S("stone") if x == -2147483648 else S("wood") if x == 2147483647 else Bundle().argmax()
"#);
    for (x, result) in [(0, "S(\"coal\")"), (i32::MIN, "S(\"stone\")"), (i32::MAX, "S(\"wood\")"), (1, "Bundle().argmax()"), (-1, "Bundle().argmax()"), (-2, "Bundle().argmax()") ] {
        src.push_str(&format!("\ntest \"key {x}\":\n    set x = {x}\n    run 40 ticks\n    assert r == {result}\n"));
    }
    let c = verify(&src, true);
    assert_eq!(made(&c, "one-hot"), 1);
    assert_eq!(made(&c, "index"), 1);
}

#[test]
fn two_nonzero_keys_use_one_lookup_without_an_index() {
    let src = r#"input x: int @ X
output r: Signal
every tick:
    r = S("coal") if x == 1 else S("stone") if x == -2147483648 else Bundle().argmax()

test "keys and absence":
    set x = 1
    run 10 ticks
    assert r == S("coal")
    set x = -2147483648
    run 10 ticks
    assert r == S("stone")
    set x = 0
    run 10 ticks
    assert r == Bundle().argmax()
    set x = 2
    run 10 ticks
    assert r == Bundle().argmax()
"#;
    let c = verify(src, false);
    assert_eq!(made(&c, "one-hot"), 1);
    assert_eq!(made(&c, "index"), 0);
}

#[test]
fn two_keys_including_zero_keep_the_one_tick_dispatch() {
    let src = r#"input x: int @ X
output r: Signal
every tick:
    r = S("coal") if x == 0 else S("stone") if x == 2 else Bundle().argmax()

test "keys and absence":
    set x = 0
    run 10 ticks
    assert r == S("coal")
    set x = 2
    run 10 ticks
    assert r == S("stone")
    set x = 1
    run 10 ticks
    assert r == Bundle().argmax()
"#;
    let c = verify(src, false);
    assert_eq!(made(&c, "one-hot"), 0, "a shifted two-arm lookup would only tie");
    assert_eq!(made(&c, "index"), 0);
}
