use ticky_compiler::{compile, Compiled, Options};
use ticky_compiler::testrun::{Harness, PVal};
use ticky_factorio::*;

fn count(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.kind.is_combinator()).count()
}

#[test]
fn compact_west_outputs_save_one_gate_and_one_tick() {
    let src = "input x: int @ X\ninput b: Bundle\noutput y: int @ Y\noutput out: Bundle\nevery tick:\n    y = x + 7\n    out = b\n    assert x != 3\n";
    for anneal in [None, Some(ticky_compiler::place::AnnealOpts { effort: 0.1, ..Default::default() })] {
        let normal = compile(src, &Options { outputs_west: true, checks: true, anneal, ..Default::default() }).unwrap();
        let compact = compile(src, &Options { outputs_west: true, compact_outputs: true, checks: true, anneal, ..Default::default() }).unwrap();
        let outs: Vec<_> = normal.program.ports.iter().enumerate().filter(|(_, p)| p.dir == ticky_syntax::ast::PortDir::Output).map(|(i, _)| i).collect();
        assert_eq!(count(&normal) - count(&compact), outs.len());
        assert!(compact.cg.netlist.validate(true).is_empty());
        assert!(!compact.cg.netlist.entities.iter().any(|e| matches!(e.role, Role::OutputGate { .. })));
        let mut n = Harness::new(&normal);
        let mut c = Harness::new(&compact);
        let mut previous: Vec<_> = outs.iter().map(|&p| c.get(p)).collect();
        let mut saw_error = false;
        for tick in 0..100 {
            let on = !matches!(tick, 11 | 26..=31 | 61..=63);
            n.sim.set_constant_on(normal.cg.run_switch, on);
            c.sim.set_constant_on(compact.cg.run_switch, on);
            for h in [&mut n, &mut c] {
                h.set(0, PVal::Int(if tick >= 80 { 3 } else { (tick * 17) % 31 - 15 }));
                h.set(1, PVal::Bun(vec![(normal.program.ports[0].sig, tick - 40)]));
                h.sim.step();
            }
            assert_eq!(outs.iter().map(|&p| n.get(p)).collect::<Vec<_>>(), previous, "tick {tick}");
            previous = outs.iter().map(|&p| c.get(p)).collect();
            saw_error |= c.get(compact.program.error_port.unwrap()) != PVal::Int(0);
        }
        assert!(saw_error, "the trace must exercise a nonzero error output");
    }
    assert!(compile(src, &Options { compact_outputs: true, ..Default::default() }).is_err());
}
