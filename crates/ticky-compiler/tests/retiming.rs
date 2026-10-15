//! Retiming of pipelined blocks (pipeline/retime.rs): the retimed schedules must save
//! combinators where they're kept and leave every output tick-exact.

use std::path::Path;

use ticky_compiler::testrun::{Harness, PVal};
use ticky_compiler::{codegen, compile, layout, program, Compiled, Options};
use ticky_syntax::ast::PortDir;

fn combinators(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count()
}

/// The program compiled as usual and as it was before retiming (no retimed schedules).
fn with_and_without(src: &str) -> (Compiled, Compiled) {
    let c = compile(src, &Options::default()).unwrap_or_else(|d| panic!("{}", d[0].message));
    let module = ticky_syntax::parse(src).unwrap();
    let mut p = program::analyze(&module, true).unwrap();
    for b in &mut p.blocks {
        if let Some(pipe) = &mut b.pipe {
            pipe.taus.truncate(pipe.retimed);
        }
    }
    let mut cg = codegen::codegen(&p, false, false).unwrap();
    // Layout connects the wires.
    let lo = layout::LayoutOpts { poles: true, outputs_west: false, ports_ew: false, anneal: None, screens: Vec::new(), controls_at: Vec::new() };
    layout::layout(&mut cg.netlist, &cg.nets, &lo).unwrap();
    let mut old = compile(src, &Options::default()).unwrap();
    old.cg = cg;
    old.program = p;
    (c, old)
}

/// Runs both circuits on the same inputs (`set` gives each tick's input values, and whether
/// RUN is on) and checks every output agrees on every tick.
fn same_trace(new: &Compiled, old: &Compiled, ticks: i32, set: &dyn Fn(i32) -> (Vec<(&'static str, PVal)>, bool)) {
    let mut a = Harness::new(new);
    let mut b = Harness::new(old);
    let outputs: Vec<usize> = (0..new.program.ports.len()).filter(|&i| new.program.ports[i].dir == PortDir::Output).collect();
    let mut changes = 0;
    let mut last = Vec::new();
    for tick in 0..ticks {
        let (values, run) = set(tick);
        for h in [&mut a, &mut b] {
            h.sim.set_constant_on(h.c.cg.run_switch, run);
            for (name, v) in &values {
                h.set(h.c.program.port_index(name).unwrap(), v.clone());
            }
            h.sim.step();
        }
        let got: Vec<PVal> = outputs.iter().map(|&o| a.get(o)).collect();
        let want: Vec<PVal> = outputs.iter().map(|&o| b.get(o)).collect();
        assert_eq!(got, want, "tick {tick}");
        changes += (got != last) as usize;
        last = got;
    }
    assert!(changes > ticks as usize / 20, "the outputs should move ({changes} changes)");
}

#[test]
fn histogram_reads_its_array_early() {
    // `far = wide[ask * 6]`: reading the 400-element array as soon as `ask * 6` is ready
    // delays one scalar on the carry wires instead of both banks of the array (7 ticks
    // each). 62 → 57 combinators for the block.
    let src = std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/histogram.ticky")).unwrap();
    let (new, old) = with_and_without(&src);
    same_trace(&new, &old, 700, &|t| {
        let sample = (t / 7 * 37 + t % 5) % 70;
        let strobe = (t / 4) % 3 == 0;
        let ask = (t / 11 * 13) % 64;
        let run = !(300..304).contains(&t) && !(500..530).contains(&t);
        (vec![("sample", PVal::Int(sample)), ("strobe", PVal::Int(strobe as i32)), ("ask", PVal::Int(ask))], run)
    });
    assert!(combinators(&new) + 5 <= combinators(&old), "{} vs {} combinators", combinators(&new), combinators(&old));
    assert_eq!(new.cg.blocks[0].latency, old.cg.blocks[0].latency);
}

#[test]
fn bundle_reads_and_scalars_each_at_their_best_tick() {
    // Neither the late nor the early schedule is best: `len(w)` and `w.total()` are taken as
    // soon as `w` arrives (so `w` itself is never delayed), while `(z + x) ^ 34` stays late.
    // Found by fuzz_pipes. 10 → 9 combinators for the block.
    let src = r#"input x: int @ X
input z: int @ Z
input w: Bundle
output e0: int @ E
output e1: int @ F
output e2: int @ G
every tick:
    e0 = 39 - len(w)
    e1 = (z == -9) + len(w)
    e2 = ((z + x) ^ 34) * w.total()
"#;
    let (new, old) = with_and_without(src);
    let t = ticky_factorio::SignalTable::base();
    let (coal, iron) = (t.lookup("coal").unwrap(), t.lookup("iron-plate").unwrap());
    same_trace(&new, &old, 300, &move |tick| {
        let w = if tick % 9 == 4 { vec![] } else { vec![(coal, tick % 13 - 6), (iron, tick / 3 % 17)] };
        let w = w.into_iter().filter(|(_, v)| *v != 0).collect();
        let run = !(150..153).contains(&tick) && !(200..220).contains(&tick);
        let z = if tick % 5 == 0 { -9 } else { tick % 7 };
        (vec![("x", PVal::Int(tick * 7 % 41 - 20)), ("z", PVal::Int(z)), ("w", PVal::Bun(w))], run)
    });
    assert!(combinators(&new) < combinators(&old), "{} vs {} combinators", combinators(&new), combinators(&old));
    assert_eq!(new.cg.blocks[0].latency, old.cg.blocks[0].latency);
}

#[test]
fn every_schedule_of_every_example_is_legal() {
    // The retiming constraints accept every schedule the pipeliner makes (they describe the
    // same space), and the retimed ones keep each block's latency.
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut retimed = 0;
    for entry in std::fs::read_dir(dir).unwrap() {
        let path = entry.unwrap().path();
        if path.extension().is_none_or(|e| e != "ticky") {
            continue;
        }
        let src = std::fs::read_to_string(&path).unwrap();
        let module = ticky_syntax::parse(&src).unwrap();
        let Ok(p) = program::analyze(&module, true) else { continue };
        for b in &p.blocks {
            let Some(pipe) = &b.pipe else { continue };
            for (i, tau) in pipe.taus.iter().enumerate() {
                assert!(pipe.space.legal(&b.graph, &pipe.transparent, tau), "{}: schedule {i}", path.display());
            }
            retimed += pipe.taus.len() - pipe.retimed;
        }
    }
    assert!(retimed > 0);
}
