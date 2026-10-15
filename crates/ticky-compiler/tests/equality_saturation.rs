//! The e-graph pass (egraph.rs, PLAN.md §3): forms the constructors don't reach, kept only
//! when the whole build is no larger and no slower.

use ticky_compiler::testrun::run_tests;
use ticky_compiler::{compile, egraph, Compiled, Opt, Options};

fn combinators(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count()
}

fn build(src: &str, opt: Opt, egraph_on: bool) -> Compiled {
    egraph::set_enabled(egraph_on);
    let c = compile(src, &Options { label: "test".into(), opt, ..Default::default() });
    egraph::set_enabled(true);
    let c = c.unwrap_or_else(|d| panic!("{}", d[0].message));
    for r in run_tests(&c, src) {
        assert!(r.failure.is_none(), "test {} failed (e-graph {egraph_on})", r.name);
    }
    c
}

/// `d + d` of `d = x * 3` is `x * 6`; `x - y == 0` is `x == y`. Both builds pass the tests.
const SRC: &str = r#"input x: int @ X
input y: int @ Y
input c: int @ C
output o: int @ O
output p: int @ P
output q: bool @ Q
every 10 ticks:
    v = y
    for i in range(3):
        if c > i:
            v = x * (i + 2)
        else:
            v = v + 1
    o = v
    d = x * 3
    p = d + d
    q = x - y == 0

test "behaviour":
    set x = 5
    set y = 5
    set c = 2
    run 30 ticks
    assert o == 16 and p == 30 and q
    set y = 7
    set c = 0
    run 30 ticks
    assert o == 10 and p == 30 and not q
    set x = -2147483648
    set y = 2147483647
    set c = 1
    run 30 ticks
    assert o == 2 and p == 0 and not q
"#;

#[test]
fn rewrites_save_combinators() {
    let depth = |c: &Compiled| c.program.blocks.iter().map(|b| b.period).collect::<Vec<_>>();
    // The pass's own win, without select picks (fuse/superopt.rs), which make some of the
    // same selects cheaper already.
    ticky_compiler::fuse::superopt::set_picks_disabled(true);
    for opt in [Opt::Speed, Opt::Size] {
        let (with, without) = (build(SRC, opt, true), build(SRC, opt, false));
        let (w, p) = (combinators(&with), combinators(&without));
        assert!(w + 2 <= p, "{opt:?}: {w} combinators with the e-graph pass, {p} without");
        assert!(depth(&with).iter().zip(depth(&without)).all(|(a, b)| *a <= b));
    }
    ticky_compiler::fuse::superopt::set_picks_disabled(false);
    // With picks: still never larger or slower.
    for opt in [Opt::Speed, Opt::Size] {
        let (with, without) = (build(SRC, opt, true), build(SRC, opt, false));
        let (w, p) = (combinators(&with), combinators(&without));
        assert!(w <= p, "{opt:?} with picks: {w} combinators with the e-graph pass, {p} without");
        assert!(depth(&with).iter().zip(depth(&without)).all(|(a, b)| *a <= b));
    }
}

/// A program the pass doesn't improve is built exactly as without it.
#[test]
fn no_gain_no_change() {
    let src = "input x: int @ X\noutput o: int @ O\nevery 10 ticks:\n    o = x * 3 + 1\n";
    let (with, without) = (build(src, Opt::Speed, true), build(src, Opt::Speed, false));
    assert_eq!(with.blueprint_string(), without.blueprint_string());
}
