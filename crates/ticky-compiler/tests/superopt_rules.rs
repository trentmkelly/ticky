//! The superoptimiser's checked-in rule table (`tools/superopt/rules.jsonl`, written by
//! `superopt search` and proved by `tools/superopt_confirm.py --write`): every rule is proved,
//! and every pattern Ticky can spell, compiled as a program, behaves the same with and without
//! codegen's picks (the rule family the compiler implements) and never costs more with them.
use ticky_compiler::fuse::superopt::set_picks_disabled;
use ticky_compiler::testrun::{Harness, PVal};
use ticky_compiler::{compile, Compiled, Options};
use ticky_factorio::netlist::Kind;

const RULES: &str = include_str!("../../../tools/superopt/rules.jsonl");

fn combinators(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| matches!(e.kind, Kind::Arith(_) | Kind::Decider(_) | Kind::Selector(_))).count()
}

fn build(src: &str, picks: bool) -> Compiled {
    set_picks_disabled(!picks);
    let c = compile(src, &Options::default());
    set_picks_disabled(false);
    c.unwrap_or_else(|e| panic!("{src}\n{e:?}"))
}

#[test]
fn rules_are_proved_and_picks_implement_them() {
    let (mut tried, mut smaller) = (0, 0);
    let mut rules = 0;
    for line in RULES.lines().filter(|l| !l.trim().is_empty()) {
        let r: serde_json::Value = serde_json::from_str(line).unwrap();
        rules += 1;
        assert_eq!(r["proved"], "unsat", "rule not proved: {}", r["shape"]);
        let Some(t) = r["ticky"].as_object() else { continue };
        let expr = t["expr"].as_str().unwrap();
        let bools: Vec<usize> = t["bools"].as_array().unwrap().iter().map(|b| b.as_u64().unwrap() as usize).collect();
        let n = r["leaves"].as_array().unwrap().len();
        let names = ["a", "b", "c"];
        let mut src = String::new();
        for (i, nm) in names.iter().enumerate().take(n) {
            let ty = if bools.contains(&i) { "bool" } else { "int" };
            src += &format!("input {nm}: {ty} @ {}\n", nm.to_uppercase());
        }
        src += &format!("input z: int @ Z\noutput o: int @ O\nevery 20 ticks:\n    o = ({expr}) ^ z\n");
        let (on, off) = (build(&src, true), build(&src, false));
        tried += 1;
        assert!(combinators(&on) <= combinators(&off), "{expr}: {} > {}", combinators(&on), combinators(&off));
        smaller += (combinators(&on) < combinators(&off)) as usize;
        // Same outputs, tick by tick, on edge values.
        let values = [0, 1, -1, 2, 5, -7, 40, i32::MAX, i32::MIN, i32::MIN + 1];
        let (mut ha, mut hb) = (Harness::new(&on), Harness::new(&off));
        let port = |c: &Compiled, nm: &str| c.program.port_index(nm).unwrap();
        for (k, &v) in values.iter().enumerate() {
            for (i, nm) in names.iter().enumerate().take(n) {
                let x = if bools.contains(&i) { ((k >> i) & 1) as i32 } else { values[(k * (i + 3) + i) % values.len()] };
                let x = if i == 1 && k % 3 == 0 && !bools.contains(&i) && !bools.contains(&0) { values[k] } else { x };
                ha.set(port(&on, nm), PVal::Int(x));
                hb.set(port(&off, nm), PVal::Int(x));
            }
            ha.set(port(&on, "z"), PVal::Int(v));
            hb.set(port(&off, "z"), PVal::Int(v));
            for tick in 0..45 {
                ha.sim.step();
                hb.sim.step();
                assert_eq!(ha.get(port(&on, "o")), hb.get(port(&off, "o")), "{expr}: vector {k}, tick {tick}");
            }
        }
    }
    eprintln!("{rules} rules; {tried} compiled; {smaller} smaller with picks");
    assert!(rules >= 20 && tried >= 10 && smaller * 2 >= tried, "{rules} rules, {tried} compiled, {smaller} smaller");
}
