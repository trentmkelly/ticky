//! Select picks (codegen/selects.rs `Out::Pick`, found by the superoptimiser, PLAN.md §4):
//! a select's runtime arms copied off the bus by one decider (`each` over a code table on red,
//! the arm conditions on green, one output summing what passes). Each program is built with and
//! without picks and run in lockstep on edge values: the outputs must agree every tick, and the
//! picked build must be smaller and no slower.
use ticky_compiler::fuse::superopt::set_picks_disabled;
use ticky_compiler::testrun::{Harness, PVal};
use ticky_compiler::{compile, Compiled, Opt, Options};
use ticky_factorio::netlist::Kind;

const SHAPES: &str = "\
input x: int @ X
input y: int @ Y
input z: int @ Z
output o0: int @ A
output o1: int @ B
output o2: int @ C
output o3: int @ D
output o4: int @ E
output o5: int @ F
output o6: int @ G
output o7: int @ H
output o8: int @ I
output o9: int @ J
output o10: int @ K
output o11: int @ L
output o12: int @ M
output o13: int @ N
BLOCK
    o0 = min(x, y)
    o1 = max(x, y) + z
    o2 = x if y > 3 else z
    o3 = abs(x) ^ y
    o4 = x % y
    o5 = x // y
    o6 = (x if z == 0 else y) * 2
    o7 = (y if x > 0 else 0) - z
    o8 = x if x > y else (y if y > z else z)
    o9 = (min(x, z) + 3) ^ y
    o10 = (max(y, z) + 3) ^ x
    o11 = (x if x != 0 else y) + x
    o12 = (z % x) + y
    o13 = min(x, x + 1)
";

fn combinators(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| matches!(e.kind, Kind::Arith(_) | Kind::Decider(_) | Kind::Selector(_))).count()
}

fn picks(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| e.description.as_deref().is_some_and(|d| d.contains("off the bus)"))).count()
}

fn build(src: &str, opts: &Options, picks: bool) -> Compiled {
    set_picks_disabled(!picks);
    let c = compile(src, opts).unwrap();
    set_picks_disabled(false);
    assert!(c.cg.netlist.validate(true).is_empty());
    c
}

/// Runs both builds on the same inputs, tick by tick; every output must agree on every tick
/// (same values, same latency).
fn lockstep(a: &Compiled, b: &Compiled, outputs: usize, hold: usize) {
    let values = [0, 1, -1, 2, 3, 4, -7, 1000, i32::MAX, i32::MIN, i32::MAX - 1, i32::MIN + 1];
    let (mut ha, mut hb) = (Harness::new(a), Harness::new(b));
    let port = |c: &Compiled, n: &str| c.program.port_index(n).unwrap();
    let mut n = 0;
    for (i, &x) in values.iter().enumerate() {
        for (j, &y) in values.iter().enumerate() {
            // z sometimes equal to x or y (ties), sometimes 0 (a missing signal).
            let z = match (i + 2 * j) % 4 {
                0 => x,
                1 => y,
                2 => 0,
                _ => values[(i * 5 + j * 7) % values.len()],
            };
            for (h, c) in [(&mut ha, a), (&mut hb, b)] {
                h.set(port(c, "x"), PVal::Int(x));
                h.set(port(c, "y"), PVal::Int(y));
                h.set(port(c, "z"), PVal::Int(z));
            }
            for t in 0..hold {
                ha.sim.step();
                hb.sim.step();
                for k in 0..outputs {
                    let o = format!("o{k}");
                    let (va, vb) = (ha.get(port(a, &o)), hb.get(port(b, &o)));
                    assert_eq!(va, vb, "{o}: x={x} y={y} z={z}, tick {t} after setting them");
                }
            }
            n += 1;
        }
    }
    assert_eq!(n, values.len() * values.len());
}

fn int(h: &Harness, c: &Compiled, n: &str) -> i32 {
    match h.get(c.program.port_index(n).unwrap()) {
        PVal::Int(v) => v,
        v => panic!("{n}: {v:?}"),
    }
}

#[test]
fn picks_agree_with_multipliers_in_periodic_blocks() {
    let src = SHAPES.replace("BLOCK", "every 20 ticks:");
    for opt in [Opt::Speed, Opt::Size] {
        let opts = Options { opt, ..Default::default() };
        let (on, off) = (build(&src, &opts, true), build(&src, &opts, false));
        assert!(picks(&on) >= 8, "{opt:?}: {} picks", picks(&on));
        assert_eq!(picks(&off), 0);
        assert!(combinators(&on) + 20 <= combinators(&off), "{opt:?}: {} vs {}", combinators(&on), combinators(&off));
        lockstep(&on, &off, 14, 45);
    }
}

#[test]
fn picks_agree_in_the_main_program_and_with_checks() {
    let src = SHAPES.replace("BLOCK", "while True:") + "    wait 1\n";
    for checks in [false, true] {
        let opts = Options { checks, ..Default::default() };
        let (on, off) = (build(&src, &opts, true), build(&src, &opts, false));
        assert!(picks(&on) >= 8);
        assert!(combinators(&on) < combinators(&off));
        lockstep(&on, &off, 14, 30);
    }
}

#[test]
fn picks_compute_the_right_values() {
    let src = SHAPES.replace("BLOCK", "every 20 ticks:");
    let c = build(&src, &Options::default(), true);
    let mut h = Harness::new(&c);
    let port = |n: &str| c.program.port_index(n).unwrap();
    for (x, y, z) in [(5, -3, 0), (0, 0, 0), (i32::MIN, i32::MAX, 7), (-7, 2, -7), (9, 9, 1)] {
        h.set(port("x"), PVal::Int(x));
        h.set(port("y"), PVal::Int(y));
        h.set(port("z"), PVal::Int(z));
        for _ in 0..45 {
            h.sim.step();
        }
        assert_eq!(int(&h, &c, "o0"), x.min(y));
        assert_eq!(int(&h, &c, "o1"), x.max(y).wrapping_add(z));
        assert_eq!(int(&h, &c, "o2"), if y > 3 { x } else { z });
        // Python's `%` (sign of the divisor); x % 0 == 0.
        let fm = if y == 0 || y == -1 {
            0
        } else {
            let r = x % y;
            if r != 0 && (r < 0) != (y < 0) { r + y } else { r }
        };
        assert_eq!(int(&h, &c, "o4"), fm, "x % y, x={x} y={y}");
        assert_eq!(int(&h, &c, "o8"), if x > y { x } else if y > z { y } else { z });
        assert_eq!(int(&h, &c, "o11"), (if x != 0 { x } else { y }).wrapping_add(x));
    }
}

#[test]
fn register_arms_named_like_the_result() {
    // The arms are the registers being loaded (`best = max(best, x)`): the pick reads the
    // register's signal from the bus and writes the same signal onto the staging wire.
    let src = "\
input x: int @ X
input reset: bool @ R
output best: int @ B
output worst: int @ W
every 10 ticks:
    if reset:
        best = 0
        worst = 0
    else:
        best = max(best, x)
        worst = min(worst, x - 1)
";
    for opt in [Opt::Speed, Opt::Size] {
        let opts = Options { opt, ..Default::default() };
        let (on, off) = (build(src, &opts, true), build(src, &opts, false));
        assert!(combinators(&on) <= combinators(&off));
        let mut hs = [Harness::new(&on), Harness::new(&off)];
        for (i, x) in [3, -5, 7, 0, i32::MAX, i32::MIN + 1, 2].into_iter().enumerate() {
            for h in &mut hs {
                h.set(on.program.port_index("x").unwrap(), PVal::Int(x));
                h.set(on.program.port_index("reset").unwrap(), PVal::Int((i == 3) as i32));
            }
            for _ in 0..25 {
                for h in &mut hs {
                    h.sim.step();
                }
                for o in ["best", "worst"] {
                    let p = on.program.port_index(o).unwrap();
                    assert_eq!(hs[0].get(p), hs[1].get(p), "{o} after x={x}");
                }
            }
        }
    }
}

#[test]
fn min_of_two_inputs_is_one_decider() {
    // 5 combinators before (two conditions, two `x * c`, the `+ c`), now 1: the pick decider
    // with `c` as an always-on term. (Its value settles in 1 tick instead of 3; the block's
    // schedule, made before codegen, is unchanged.)
    let src = "input a: int @ A\ninput b: int @ B\ninput c: int @ C\noutput o: int @ O\nevery 60 ticks:\n    o = min(a, b) + c\n";
    let on = build(src, &Options::default(), true);
    let off = build(src, &Options::default(), false);
    assert_eq!(picks(&on), 1);
    assert_eq!(combinators(&off) - combinators(&on), 4, "the pick takes the sum too");
}

#[test]
fn every_tick_blocks_are_unchanged() {
    // Pipelined blocks have their own emitter, which doesn't pick.
    let src = SHAPES.replace("BLOCK", "every tick:");
    let on = build(&src, &Options::default(), true);
    let off = build(&src, &Options::default(), false);
    assert_eq!(picks(&on), 0);
    assert_eq!(combinators(&on), combinators(&off));
}

#[test]
fn picks_read_packed_lanes_and_wire_sums() {
    // `p`, `q`, `r`, `t` are lanes of one `* 3` pack (straight-line vectorisation) that picks
    // read off the bus; `s` is a wire sum (its operands write its signal), read by a pick too.
    // (A select is never a lane's input: SLP leaves select stages alone. Selects are wrapped in
    // `^`: an output's own select becomes guarded register loads, not a stage.)
    let src = "\
input x: int @ X
input y: int @ Y
input z: int @ Z
output o0: int @ A
output o1: int @ B
output o2: int @ C
output o3: int @ D
output o4: int @ E
every 20 ticks:
    p = (x ^ y) * 3
    q = (y ^ z) * 3
    r = (x & z) * 3
    t = (x | y) * 3
    s = x * 2 + y * 3
    o0 = (p if z > 0 else q) ^ x
    o1 = max(r, t) ^ y
    o2 = p ^ t
    o3 = (s if z > 0 else y) ^ z
    o4 = s ^ 7
";
    for opt in [Opt::Speed, Opt::Size] {
        let opts = Options { opt, ..Default::default() };
        let (on, off) = (build(src, &opts, true), build(src, &opts, false));
        let packs = on.cg.netlist.entities.iter().filter(|e| e.description.as_deref().is_some_and(|d| d.contains("lanes at once"))).count();
        assert_eq!(packs, 1, "{opt:?}");
        assert_eq!(picks(&on), 3, "{opt:?}");
        assert!(combinators(&on) < combinators(&off));
        lockstep(&on, &off, 5, 45);
    }
}
