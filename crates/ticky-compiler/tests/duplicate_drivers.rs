//! Duplicated drivers (`--duplicate-drivers`, always on with `--place=anneal`): copies of
//! cheap combinators placed beside far members of their networks, where that saves relays.
//! The copies must change nothing but the wiring: every example's layout stays valid, its
//! tests pass, and in lockstep with the build without copies every original entity (and
//! every copy, like its original) outputs the same on every tick.

use std::path::Path;

use ticky_compiler::program::Ty;
use ticky_compiler::testrun::{run_tests, Harness, PVal};
use ticky_compiler::{compile, Compiled, Options};
use ticky_syntax::ast::PortDir;

const MARK: &str = "(copy, saves wire relays)";

fn examples() -> Vec<(String, String)> {
    let dir = Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut v: Vec<(String, String)> = std::fs::read_dir(&dir)
        .unwrap()
        .map(|e| e.unwrap().path())
        .filter(|p| p.extension().is_some_and(|e| e == "ticky"))
        .map(|p| (p.display().to_string(), std::fs::read_to_string(&p).unwrap()))
        .collect();
    v.sort();
    v
}

fn copies(c: &Compiled) -> Vec<usize> {
    let n = &c.cg.netlist;
    (0..n.entities.len()).filter(|&i| n.entities[i].description.as_deref().is_some_and(|d| d.ends_with(MARK))).collect()
}

fn entities(c: &Compiled) -> usize {
    c.cg.netlist.entities.len()
}

/// Random inputs (a small deterministic generator), the same for both builds; every output
/// of every entity both builds share, and each copy's output, compared every tick.
fn lockstep(name: &str, a: &Compiled, b: &Compiled, ticks: u64) {
    let t = ticky_factorio::SignalTable::base();
    let items: Vec<ticky_factorio::Sig> = ["iron-plate", "copper-plate", "coal"].iter().map(|s| t.lookup(s).unwrap()).collect();
    let mut seed: u64 = 0x5EED;
    let mut rnd = |n: u64| {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (seed >> 33) % n
    };
    let (mut ha, mut hb) = (Harness::new(a), Harness::new(b));
    // Entities codegen made (ports, combinators, lamps) come first in both; then poles.
    let shared = a.cg.netlist.entities.iter().position(|e| matches!(e.kind, ticky_factorio::Kind::Pole)).unwrap_or(entities(a));
    let nb = &b.cg.netlist;
    let originals: Vec<(usize, Vec<usize>)> = copies(b)
        .into_iter()
        .map(|k| {
            let d = nb.entities[k].description.as_deref().unwrap().trim_end_matches(MARK).trim_end();
            let of: Vec<usize> = (0..shared).filter(|&i| nb.entities[i].description.as_deref().unwrap_or("") == d).collect();
            assert!(!of.is_empty(), "{name}: no original for copy {k}");
            (k, of)
        })
        .collect();
    for tick in 0..ticks {
        if tick % 5 == 0 {
            for (i, p) in a.program.ports.iter().enumerate() {
                if p.dir != PortDir::Input {
                    continue;
                }
                let v = match p.ty {
                    Ty::Bool => PVal::Int(rnd(2) as i32),
                    Ty::Int => PVal::Int(rnd(41) as i32 - 20),
                    Ty::Bundle => {
                        let mut b = Vec::new();
                        for &s in &items {
                            if rnd(2) == 1 {
                                b.push((s, rnd(201) as i32 - 100));
                            }
                        }
                        PVal::Bun(b)
                    }
                    Ty::Signal => PVal::Bun(items.iter().take(rnd(4) as usize).skip(rnd(2) as usize).take(1).map(|&s| (s, 1)).collect()),
                };
                ha.set(i, v.clone());
                hb.set(i, v);
            }
        }
        ha.sim.step();
        hb.sim.step();
        for e in 0..shared {
            assert_eq!(ha.sim.outputs_of(e), hb.sim.outputs_of(e), "{name}: entity {e} differs at tick {tick}");
        }
        for (k, of) in &originals {
            assert!(of.iter().any(|&o| hb.sim.outputs_of(*k) == hb.sim.outputs_of(o)), "{name}: copy {k} differs from its original at tick {tick}");
        }
    }
}

#[test]
fn duplicated_drivers_save_relays_and_change_nothing_else() {
    let (mut relays_before, mut relays_after, mut changed) = (0, 0, 0);
    for (name, src) in examples() {
        let checks = src.starts_with("# ticky: --checks");
        for (poles, outputs_west, ports_ew) in [(true, false, false), (false, true, false), (true, true, true)] {
            let base = Options { label: "test".into(), checks, poles, outputs_west, ports_ew, ..Default::default() };
            let a = compile(&src, &base).unwrap_or_else(|d| panic!("{name}: {}", d[0].message));
            let b = compile(&src, &Options { duplicate_drivers: true, ..base }).unwrap_or_else(|d| panic!("{name} (duplicated): {}", d[0].message));
            assert!(b.cg.netlist.validate(poles).is_empty(), "{name} (poles {poles}): {:?}", b.cg.netlist.validate(poles));
            relays_before += a.layout.relays;
            relays_after += b.layout.relays;
            let k = copies(&b).len();
            if k == 0 {
                assert_eq!(a.blueprint_string(), b.blueprint_string(), "{name}: changed without copies");
                continue;
            }
            changed += 1;
            // Kept only when it saves entities, and the footprint doesn't grow.
            assert!(b.layout.relays + k < a.layout.relays, "{name}: {k} copies for {} → {} relays", a.layout.relays, b.layout.relays);
            assert!(entities(&b) < entities(&a), "{name}");
            // (It can shrink: relays that stuck out of the block may go.)
            assert!(b.layout.width <= a.layout.width && b.layout.height <= a.layout.height, "{name}");
            assert_eq!(a.layout.poles, b.layout.poles, "{name}");
            for r in run_tests(&b, &src) {
                if let Some(d) = r.failure {
                    panic!("{name} (duplicated, poles {poles}): test {} failed:\n{}", r.name, d.render(&name, &src));
                }
            }
            lockstep(&name, &a, &b, 400);
        }
    }
    // The win, pinned loosely (other passes move the numbers): a third of the grid's relays
    // go, in several examples.
    assert!(relays_after * 3 <= relays_before * 2, "relays {relays_before} → {relays_after}");
    assert!(changed >= 6, "{changed} builds changed");
}

/// Sorting's eight lanes read constants from across the grid: copies of them sit beside the
/// readers instead of relaying.
#[test]
fn sorting_reads_constants_nearby() {
    let src = std::fs::read_to_string(Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples/sorting.ticky")).unwrap();
    let a = compile(&src, &Options::default()).unwrap();
    let b = compile(&src, &Options { duplicate_drivers: true, ..Default::default() }).unwrap();
    assert!(b.layout.relays + 10 <= a.layout.relays, "relays {} → {}", a.layout.relays, b.layout.relays);
    assert!(copies(&b).len() + b.layout.relays < a.layout.relays);
}

/// Annealed placement duplicates by default (and `AnnealOpts::duplicate` turns it off);
/// whatever it does keeps the layout valid and the tests passing.
#[test]
fn annealed_layouts_duplicate_by_default() {
    let on = ticky_compiler::place::AnnealOpts { effort: 0.2, ..Default::default() };
    assert!(on.duplicate);
    let off = ticky_compiler::place::AnnealOpts { duplicate: false, ..on };
    for (name, src) in examples() {
        let checks = src.starts_with("# ticky: --checks");
        for poles in [true, false] {
            let o = |a| Options { label: "test".into(), checks, poles, anneal: Some(a), ..Default::default() };
            let b = compile(&src, &o(on)).unwrap();
            if copies(&b).is_empty() {
                continue;
            }
            let a = compile(&src, &o(off)).unwrap();
            assert!(b.cg.netlist.validate(poles).is_empty(), "{name}");
            assert!(b.layout.relays + copies(&b).len() < a.layout.relays, "{name}");
            for r in run_tests(&b, &src) {
                assert!(r.failure.is_none(), "{name} (annealed, duplicated): test {} failed", r.name);
            }
            lockstep(&name, &a, &b, 300);
        }
    }
}
