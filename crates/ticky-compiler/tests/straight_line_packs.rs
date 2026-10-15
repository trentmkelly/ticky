//! Straight-line vectorisation (fuse/slp.rs): same-shape scalar operations done by one `each`
//! combinator, exact for every value (missing signals included), in periodic blocks and the
//! main program.
use ticky_compiler::testrun::{Harness, PVal};
use ticky_compiler::{compile, Compiled, Opt, Options};
use ticky_factorio::netlist::Kind;

/// Lanes of five families: a shared constant (`* 3`, `>> 2`), a table (`+ k_i`, mixed `<< k_i`),
/// comparisons; each lane's input a combinator only it reads, its result read by more logic.
const LANES: &str = "\
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
BLOCK
    o0 = ((x ^ y) * 3) ^ z
    o1 = ((y ^ z) * 3) ^ x
    o2 = ((x & z) * 3) ^ y
    o3 = ((x * y) + 5) ^ z
    o4 = ((y * z) + 7) ^ x
    o5 = ((x * z) - 1000) ^ y
    o6 = ((x | y) << 1) ^ z
    o7 = ((y | z) << 4) ^ x
    o8 = ((x | z) << 9) ^ y
    o9 = ((x ^ z) > 5) ^ y
    o10 = ((y & z) > 5) ^ x
    o11 = ((x - y) >> 2) ^ ((y + z) >> 2)
";

fn expected(x: i32, y: i32, z: i32) -> [i32; 12] {
    [
        (x ^ y).wrapping_mul(3) ^ z,
        (y ^ z).wrapping_mul(3) ^ x,
        (x & z).wrapping_mul(3) ^ y,
        x.wrapping_mul(y).wrapping_add(5) ^ z,
        y.wrapping_mul(z).wrapping_add(7) ^ x,
        x.wrapping_mul(z).wrapping_sub(1000) ^ y,
        (x | y).wrapping_shl(1) ^ z,
        (y | z).wrapping_shl(4) ^ x,
        (x | z).wrapping_shl(9) ^ y,
        ((x ^ z) > 5) as i32 ^ y,
        ((y & z) > 5) as i32 ^ x,
        (x.wrapping_sub(y) >> 2) ^ (y.wrapping_add(z) >> 2),
    ]
}

fn combinators(c: &Compiled) -> usize {
    c.cg.netlist.entities.iter().filter(|e| matches!(e.kind, Kind::Arith(_) | Kind::Decider(_) | Kind::Selector(_))).count()
}

fn packs(c: &Compiled) -> Vec<String> {
    c.cg.netlist.entities.iter().filter_map(|e| e.description.clone()).filter(|d| d.contains("lanes at once")).collect()
}

/// Settled outputs for each input triple (0 and the extremes included: lanes see missing
/// signals and wrap).
fn check(c: &Compiled, ticks: usize) {
    let values = [0, 1, -1, 6, 1000, -123456, i32::MAX, i32::MIN];
    let mut h = Harness::new(c);
    let port = |n: &str| c.program.port_index(n).unwrap();
    for (i, &x) in values.iter().enumerate() {
        for (j, &y) in values.iter().enumerate() {
            let z = values[(i * 3 + j * 5) % values.len()];
            h.set(port("x"), PVal::Int(x));
            h.set(port("y"), PVal::Int(y));
            h.set(port("z"), PVal::Int(z));
            for _ in 0..ticks {
                h.sim.step();
            }
            let got: Vec<PVal> = (0..12).map(|k| h.get(port(&format!("o{k}")))).collect();
            let want: Vec<PVal> = expected(x, y, z).iter().map(|&v| PVal::Int(v)).collect();
            assert_eq!(got, want, "x={x} y={y} z={z}");
        }
    }
}

#[test]
fn periodic_block_packs() {
    let src = LANES.replace("BLOCK", "every 20 ticks:");
    for opt in [Opt::Speed, Opt::Size] {
        let c = compile(&src, &Options { opt, ..Default::default() }).unwrap();
        assert!(c.cg.netlist.validate(true).is_empty());
        // `* 3` (3 lanes), `+ k` table (3), mixed `<<` table (3), `> 5` (2), `>> 2` (2).
        let mut p = packs(&c);
        p.sort();
        assert_eq!(p, ["block 1: 2 lanes at once", "block 1: 2 lanes at once", "block 1: 3 lanes at once", "block 1: 3 lanes at once", "block 1: 3 lanes at once"], "{opt:?}");
        let tables = c.cg.netlist.entities.iter().filter(|e| e.description.as_deref() == Some("block 1: lane constants")).count();
        assert_eq!(tables, 2, "{opt:?}");
        // Thirteen lanes in five combinators (and two constant combinators): 62 without packs.
        assert!(combinators(&c) <= 54, "{opt:?}: {} combinators", combinators(&c));
        check(&c, 60);
    }
}

#[test]
fn main_program_packs() {
    let src = LANES.replace("BLOCK", "while True:") + "    wait 1\n";
    let c = compile(&src, &Options::default()).unwrap();
    assert_eq!(packs(&c).len(), 5);
    check(&c, 60);
}

#[test]
fn checks_keep_packs_exact() {
    let src = LANES.replace("BLOCK", "every 20 ticks:");
    let c = compile(&src, &Options { checks: true, ..Default::default() }).unwrap();
    assert_eq!(packs(&c).len(), 5);
    check(&c, 60);
}

#[test]
fn aes_rounds_pack_their_bytes() {
    // Byte extraction `(w >> k) & 255` (16 lanes, twice per round), `xtime`'s final `& 255`
    // and the S-box reads' shifts into place: 336 combinators before.
    let src = include_str!("../../../examples/aes128.ticky");
    let c = compile(src, &Options::default()).unwrap();
    assert!(combinators(&c) <= 281, "{} combinators", combinators(&c));
    assert!(packs(&c).len() >= 4);
}
