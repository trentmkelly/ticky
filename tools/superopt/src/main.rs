//! Offline superoptimiser for Ticky (PLAN.md §4): finds the fewest Factorio combinators that
//! compute a small scalar pattern harvested from the compiler (`tools/superopt_harvest.py`).
//!
//! Model. The pattern's inputs `x0…` are signals X, Y, Z on a green input network (the bus),
//! together with *noise* signals (other values on the bus, one of them sometimes equal to an
//! input). The result must appear as signal O on an output network, with nothing else there.
//! Private red networks are free: a constant combinator ("table", e.g. a signal mask) or an
//! intermediate result T. Combinators may write the same network (wire sums are free). Wildcards
//! (`each`, `anything`, `everything`) only read red networks (the bus has arbitrary signals).
//!
//! Circuits searched (n = combinators, d = depth in ticks):
//!   A  n=1 d=1   one arithmetic or decider combinator (optionally reading a table on red),
//!                plus optionally a constant combinator on the output (wire sum);
//!   B  n=2 d=1   two of those writing the output together (meet in the middle on their
//!                output signatures);
//!   S  n=2 d=2   one combinator writing a private network P (T or copies of inputs), a
//!                second reading the bus and P;
//!   C  n=3 d=2   S plus a parallel combinator of kind A on the output.
//! Every candidate is a real netlist run by ticky-sim (many candidates per netlist, sharing the
//! input constants), on test vectors with 0, ±1, INT_MIN, INT_MAX, the pattern's constants
//! (±1), equal inputs, random values, and missing (zero) signals. Winners are written with
//! their circuits as JSON lines for `tools/superopt_confirm.py`, which proves them with z3.
//!
//! usage: superopt search --targets FILE [--top N] [--seed S] [--out RULES.jsonl]
//!                        [--min-excess E] [--budget SECONDS]
//!        superopt eval 'SHAPE' X0 [X1 [X2]]

mod pat;

use std::collections::HashMap;
use std::io::Write;
use std::time::Instant;

use pat::{Pat, ALL_AR, ALL_CMP};
use ticky_factorio::{ArOp, Arith, CmpOp, Cond, ConstComb, Conn, DOut, Decider, EntId, Kind, Netlist, Nets, Operand, Role, Selector, Sig, SignalTable};
use ticky_sim::Sim;

// ------------------------------------------------------------------ random numbers

/// SplitMix64: a fixed seed gives the same vectors, hence the same results.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

// ------------------------------------------------------------------ signals

struct Sigs {
    x: Vec<Sig>,
    o: Sig,
    t: Sig,
    noise: Vec<Sig>,
    each: Sig,
    anything: Sig,
    everything: Sig,
}

impl Sigs {
    fn new() -> Self {
        let t = SignalTable::base();
        let v = |n: &str| t.lookup(n).expect(n);
        Sigs {
            x: vec![v("signal-X"), v("signal-Y"), v("signal-Z")],
            o: v("signal-O"),
            t: v("signal-T"),
            noise: vec![v("signal-N"), v("signal-M")],
            each: t.special("signal-each"),
            anything: t.special("signal-anything"),
            everything: t.special("signal-everything"),
        }
    }
}

fn name(s: Sig) -> &'static str {
    SignalTable::base().name(s)
}

// ------------------------------------------------------------------ candidates

/// What a candidate's red input reads.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Red {
    None,
    /// A constant combinator (index into the search's tables).
    Table(usize),
    /// The private network written by the first combinator of a serial circuit.
    P,
}

#[derive(Clone, Debug)]
struct Cand {
    kind: Kind,
    red: Red,
}

/// One test: the bus contents (inputs and noise).
type Bus = Vec<(Sig, i32)>;

/// Runs batches of candidates in ticky-sim: one netlist per batch, every candidate reading the
/// same input constant (green), its table or P constant (red); outputs read per entity.
struct Engine {
    tables: Vec<Vec<(Sig, i32)>>,
    evals: u64,
}

const BATCH: usize = 20_000;

impl Engine {
    /// Outputs of every candidate on every test: `f(cand, test, outputs)`. `p[test]`: the P
    /// network's contents for that test (serial circuits).
    fn run(&mut self, cands: &[Cand], tests: &[Bus], p: Option<&[Vec<(Sig, i32)>]>, f: &mut dyn FnMut(usize, usize, &[(Sig, i32)])) {
        for (bi, chunk) in cands.chunks(BATCH).enumerate() {
            let mut net = Netlist::default();
            let off = || Kind::Constant(ConstComb { values: vec![], on: true });
            let input = net.add(off(), Role::Core);
            let pc = net.add(off(), Role::Core);
            let sink_in = net.add(Kind::Constant(ConstComb { values: vec![], on: false }), Role::Core);
            let sink_out = net.add(Kind::Constant(ConstComb { values: vec![], on: false }), Role::Core);
            let tabs: Vec<EntId> = self.tables.iter().map(|t| net.add(Kind::Constant(ConstComb { values: t.clone(), on: true }), Role::Core)).collect();
            let first = net.entities.len();
            for c in chunk {
                let e = net.add(c.kind.clone(), Role::Core);
                net.wire((e, Conn::InGreen), (input, Conn::Green));
                let red = match c.red {
                    Red::None => sink_in,
                    Red::Table(i) => tabs[i],
                    Red::P => pc,
                };
                net.wire((e, Conn::InRed), (red, Conn::Red));
                net.wire((e, Conn::OutRed), (sink_out, Conn::Red));
                net.wire((e, Conn::OutGreen), (sink_out, Conn::Green));
            }
            let mut sim = Sim::new(&net);
            for (ti, bus) in tests.iter().enumerate() {
                sim.set_constant_values(input, bus.clone());
                sim.set_constant_values(pc, p.map_or(vec![], |p| p[ti].clone()));
                sim.step();
                for i in 0..chunk.len() {
                    f(bi * BATCH + i, ti, sim.outputs_of(first + i));
                }
                self.evals += chunk.len() as u64;
            }
        }
    }

    /// Each candidate's value of O on each test, if O is all it ever writes.
    fn signatures(&mut self, cands: &[Cand], tests: &[Bus], p: Option<&[Vec<(Sig, i32)>]>, o: Sig) -> Vec<Option<Vec<i32>>> {
        let mut out: Vec<Option<Vec<i32>>> = vec![Some(vec![0; tests.len()]); cands.len()];
        self.run(cands, tests, p, &mut |c, t, outs| {
            if let Some(s) = &mut out[c] {
                for &(sig, v) in outs {
                    if sig == o {
                        s[t] = v;
                    } else {
                        out[c] = None;
                        return;
                    }
                }
            }
        });
        out
    }

    /// Each candidate's full output on each test.
    fn contents(&mut self, cands: &[Cand], tests: &[Bus]) -> Vec<Vec<Vec<(Sig, i32)>>> {
        let mut out = vec![vec![Vec::new(); tests.len()]; cands.len()];
        self.run(cands, tests, None, &mut |c, t, outs| out[c][t] = outs.to_vec());
        out
    }

    /// A hash of each candidate's outputs over all tests (`None` if it ever writes one of
    /// `bad`, or never writes anything), without keeping them.
    fn content_hashes(&mut self, cands: &[Cand], tests: &[Bus], bad: &[Sig]) -> Vec<Option<u64>> {
        let mut h: Vec<u64> = vec![0xcbf2_9ce4_8422_2325; cands.len()];
        let mut ok = vec![true; cands.len()];
        let mut any = vec![false; cands.len()];
        self.run(cands, tests, None, &mut |c, t, outs| {
            let mut x = h[c] ^ (t as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15);
            for &(s, v) in outs {
                ok[c] &= !bad.contains(&s);
                any[c] = true;
                for w in [s.0 as u64, v as u32 as u64] {
                    x = (x ^ w).wrapping_mul(0x100_0000_01b3).rotate_left(17);
                }
            }
            h[c] = x;
        });
        h.into_iter().zip(ok).zip(any).map(|((h, ok), any)| (ok && any).then_some(h)).collect()
    }
}

// ------------------------------------------------------------------ generation

fn g(s: Sig) -> (Operand, Nets) {
    (Operand::Sig(s), Nets::GREEN)
}
fn r(s: Sig) -> (Operand, Nets) {
    (Operand::Sig(s), Nets::RED)
}
fn k(v: i32) -> (Operand, Nets) {
    (Operand::Const(v), Nets::BOTH)
}

fn arith(a: (Operand, Nets), op: ArOp, b: (Operand, Nets), out: Sig) -> Kind {
    Kind::Arith(Arith { first: a.0, first_nets: a.1, second: b.0, second_nets: b.1, op, out })
}

/// A decider literal: first signal (with networks), comparison, second operand.
#[derive(Clone, Copy, PartialEq, Debug)]
struct Lit {
    first: Sig,
    first_nets: Nets,
    cmp: CmpOp,
    second: (Operand, Nets),
}

fn decider(dnf: &[Vec<Lit>], outputs: Vec<DOut>) -> Kind {
    let mut conds = Vec::new();
    for t in dnf {
        for (i, l) in t.iter().enumerate() {
            conds.push(Cond { first: l.first, first_nets: l.first_nets, second: l.second.0, second_nets: l.second.1, cmp: l.cmp, and: i > 0 });
        }
    }
    Kind::Decider(Decider { conds, outputs })
}

fn dout(sig: Sig, copy: bool, constant: i32, nets: Nets) -> DOut {
    DOut { sig, copy, constant, nets }
}

/// The alphabet of one pattern's search.
struct Alpha {
    /// Input signals on the bus.
    xs: Vec<Sig>,
    consts: Vec<i32>,
    /// Literals over the bus: every leaf against every other leaf and every constant.
    lits: Vec<Lit>,
    /// The pattern's own literals and their negations.
    plits: Vec<Lit>,
    /// The pattern's own conditions as DNFs (`Pat::dnfs`).
    pdnfs: Vec<Vec<Vec<Lit>>>,
    /// Output constants worth trying (1, the constants, the pattern's few values).
    outk: Vec<i32>,
}

fn lit_of(xs: &[Sig], (op, a, b): (CmpOp, usize, Result<usize, i32>)) -> Lit {
    Lit { first: xs[a], first_nets: Nets::GREEN, cmp: op, second: match b {
        Ok(j) => g(xs[j]),
        Err(c) => k(c),
    } }
}

/// One-combinator candidates writing `out` (to the output, or to P when `to_p`), each with the
/// red inputs in `reds` (`red_sigs`: signals a red table/P can hold).
fn gen_single(a: &Alpha, s: &Sigs, out: Sig, reds: &[(Red, Vec<Sig>)], to_p: bool, wide: bool) -> Vec<Cand> {
    let mut v = Vec::new();
    for (red, rsigs) in reds {
        let red = *red;
        let has_red = red != Red::None;
        // Arithmetic operands: bus inputs, red signals, each (red), constants.
        let mut opnds: Vec<(Operand, Nets)> = a.xs.iter().map(|&x| g(x)).collect();
        opnds.extend(rsigs.iter().map(|&x| r(x)));
        let mut sigops = opnds.clone();
        if has_red {
            sigops.push(r(s.each));
        }
        opnds.extend(a.consts.iter().map(|&c| k(c)));
        if has_red {
            opnds.push(r(s.each));
        }
        for &x in &opnds {
            for &y in &opnds {
                if matches!((x.0, y.0), (Operand::Const(_), Operand::Const(_))) {
                    continue;
                }
                let uses_each = x.0 == Operand::Sig(s.each) || y.0 == Operand::Sig(s.each);
                for op in ALL_AR {
                    if uses_each && to_p {
                        v.push(Cand { kind: arith(x, op, y, s.each), red });
                    }
                    v.push(Cand { kind: arith(x, op, y, out), red });
                }
            }
        }
        // Decider literals: the alphabet's, plus red signals against bus and constants.
        let mut lits: Vec<Lit> = if wide { a.lits.clone() } else { a.plits.clone() };
        for &rs in rsigs {
            let mut seconds: Vec<(Operand, Nets)> = a.xs.iter().map(|&x| g(x)).collect();
            seconds.extend(a.consts.iter().map(|&c| k(c)));
            for sec in seconds {
                for cmp in ALL_CMP {
                    lits.push(Lit { first: rs, first_nets: Nets::RED, cmp, second: sec });
                }
            }
        }
        let mut outs: Vec<DOut> = a.outk.iter().map(|&c| dout(out, false, c, Nets::BOTH)).collect();
        if has_red {
            outs.push(dout(out, true, 0, Nets::RED));
        }
        if to_p {
            outs.extend(a.xs.iter().map(|&x| dout(x, true, 0, Nets::GREEN)));
        }
        // One literal, two (AND, OR).
        for (i, &l1) in lits.iter().enumerate() {
            for o in &outs {
                v.push(Cand { kind: decider(&[vec![l1]], vec![o.clone()]), red });
            }
            for &l2 in &lits[i + 1..] {
                for o in &outs {
                    v.push(Cand { kind: decider(&[vec![l1, l2]], vec![o.clone()]), red });
                    v.push(Cand { kind: decider(&[vec![l1], vec![l2]], vec![o.clone()]), red });
                }
            }
        }
        if has_red {
            // Wildcards over red: anything/everything/each against constants.
            for w in [s.anything, s.everything, s.each] {
                for &c in &a.consts {
                    for cmp in ALL_CMP {
                        let l = Lit { first: w, first_nets: Nets::RED, cmp, second: k(c) };
                        for o in &outs {
                            v.push(Cand { kind: decider(&[vec![l]], vec![o.clone()]), red });
                        }
                        if w == s.each {
                            // Each passing signal: its red/green value summed onto `out`.
                            v.push(Cand { kind: decider(&[vec![l]], vec![dout(out, true, 0, Nets::GREEN)]), red });
                            if to_p {
                                v.push(Cand { kind: decider(&[vec![l]], vec![dout(s.each, true, 0, Nets::GREEN)]), red });
                            }
                        }
                    }
                }
            }
        }
        if let Red::Table(_) = red {
            // Picks: one term per table signal, `each(red) = its code ∧ a literal` (or alone),
            // copying the passing signal's bus value onto `out` (summed, so renamed).
            let codes: Vec<i32> = rsigs.iter().enumerate().map(|(i, _)| i as i32 + 1).collect();
            let mut opts: Vec<Vec<Vec<Lit>>> = vec![vec![vec![]]];
            opts.extend(a.plits.iter().map(|&l| vec![vec![l]]));
            for d in &a.pdnfs {
                if !opts.contains(d) {
                    opts.push(d.clone());
                }
            }
            let mut idx = vec![0usize; codes.len()];
            loop {
                let mut dnf = Vec::new();
                for (ci, &code) in codes.iter().enumerate() {
                    for term in &opts[idx[ci]] {
                        let mut t = vec![Lit { first: s.each, first_nets: Nets::RED, cmp: CmpOp::Eq, second: k(code) }];
                        t.extend(term.iter().copied());
                        dnf.push(t);
                    }
                }
                for nets in [Nets::GREEN] {
                    v.push(Cand { kind: decider(&dnf, vec![dout(out, true, 0, nets)]), red });
                    if to_p {
                        v.push(Cand { kind: decider(&dnf, vec![dout(s.each, true, 0, nets)]), red });
                    }
                }
                // Next combination (odometer); also the subsets with a term left out.
                let mut i = 0;
                loop {
                    if i == idx.len() {
                        break;
                    }
                    idx[i] += 1;
                    if idx[i] < opts.len() {
                        break;
                    }
                    idx[i] = 0;
                    i += 1;
                }
                if i == idx.len() {
                    break;
                }
            }
        }
        if to_p {
            // Selectors read both inputs (bus included): kept for completeness.
            for max in [true, false] {
                for index in [0, 1] {
                    v.push(Cand { kind: Kind::Selector(Selector::Select { max, index }), red });
                }
            }
            v.push(Cand { kind: Kind::Selector(Selector::Count { out }), red });
        }
    }
    v
}

// ------------------------------------------------------------------ tests

struct Tests {
    bus: Vec<Bus>,
    f: Vec<i32>,
}

const QUICK: usize = 10;
/// Most distinct P contents a serial search tries (in generation order: simplest first).
const MAX_P: usize = 4000;
const NTESTS: usize = 64;

fn make_tests(p: &Pat, ivs: &[(i64, i64)], sigs: &Sigs, rng: &mut Rng) -> Tests {
    let n = p.leaves();
    let consts = p.consts();
    let mut pool: Vec<i64> = vec![0, 1, -1, 2, -2, 3, i32::MIN as i64, i32::MAX as i64, i32::MIN as i64 + 1, i32::MAX as i64 - 1, 7, -7, 100, -100];
    for &c in &consts {
        pool.extend([c as i64, c as i64 + 1, c as i64 - 1, -(c as i64)]);
    }
    let clamp = |v: i64, (lo, hi): (i64, i64)| v.clamp(lo, hi) as i32;
    let pick = |rng: &mut Rng, iv: (i64, i64)| -> i32 {
        match rng.below(4) {
            0 => clamp(iv.0 + rng.below(((iv.1 - iv.0).min(1 << 40) + 1) as usize) as i64, iv),
            1 => clamp(rng.next() as i32 as i64, iv),
            _ => clamp(pool[rng.below(pool.len())], iv),
        }
    };
    let comp = p.complements();
    let mut xs: Vec<Vec<i32>> = Vec::new();
    // The first tests: all zero, all equal, then ones that make each leaf extreme.
    xs.push(vec![0; n]);
    for _ in 0..NTESTS * 4 {
        if xs.len() >= NTESTS {
            break;
        }
        let mut x: Vec<i32> = (0..n).map(|i| pick(rng, ivs[i])).collect();
        if n > 1 && rng.below(5) == 0 {
            let j = rng.below(n);
            let v = x[j];
            for (i, xi) in x.iter_mut().enumerate() {
                *xi = clamp(v as i64, ivs[i]);
            }
        }
        for &(t, f) in &comp {
            x[f] = (x[t] == 0) as i32;
        }
        if !xs.contains(&x) {
            xs.push(x);
        }
    }
    let f: Vec<i32> = xs.iter().map(|x| p.eval(x)).collect();
    let bus = xs
        .iter()
        .enumerate()
        .map(|(ti, x)| {
            let mut b: Bus = x.iter().enumerate().filter(|(_, v)| **v != 0).map(|(i, v)| (sigs.x[i], *v)).collect();
            // Noise: a random value, and sometimes an input's value under another signal.
            b.push((sigs.noise[0], (rng.next() as i32) | 1));
            if ti % 2 == 1 && n > 0 && x[0] != 0 {
                b.push((sigs.noise[1], x[ti % n]));
            }
            b.retain(|(_, v)| *v != 0);
            b
        })
        .collect();
    Tests { bus, f }
}

// ------------------------------------------------------------------ circuits

#[derive(Clone)]
struct Circuit {
    /// (combinator, writes P rather than the output); in evaluation order.
    combs: Vec<(Cand, bool)>,
    tables: Vec<Vec<(Sig, i32)>>,
    /// A constant combinator adding this to O on the output.
    offset: i32,
    depth: u32,
}

impl Circuit {
    fn combinators(&self) -> usize {
        self.combs.len()
    }

    fn constants(&self) -> usize {
        let mut used: Vec<usize> = self.combs.iter().filter_map(|(c, _)| if let Red::Table(i) = c.red { Some(i) } else { None }).collect();
        used.sort_unstable();
        used.dedup();
        used.len() + (self.offset != 0) as usize
    }

    /// Fewer combinators, then less depth, then fewer constants.
    fn key(&self) -> (usize, u32, usize) {
        (self.combinators(), self.depth, self.constants())
    }
}

fn nets_s(n: Nets) -> &'static str {
    match (n.red, n.green) {
        (true, true) => "RG",
        (true, false) => "R",
        (false, true) => "G",
        _ => "",
    }
}

fn opnd_json(o: Operand, n: Nets) -> String {
    match o {
        Operand::Sig(s) => format!("{{\"sig\":\"{}\",\"nets\":\"{}\"}}", name(s), nets_s(n)),
        Operand::Const(c) => format!("{{\"const\":{c}}}"),
    }
}

fn kind_json(k: &Kind) -> String {
    match k {
        Kind::Arith(a) => format!(
            "{{\"type\":\"arith\",\"op\":\"{}\",\"first\":{},\"second\":{},\"out\":\"{}\"}}",
            pat::ar_py(a.op),
            opnd_json(a.first, a.first_nets),
            opnd_json(a.second, a.second_nets),
            name(a.out)
        ),
        Kind::Decider(d) => {
            let conds: Vec<String> = d
                .conds
                .iter()
                .map(|c| format!("{{\"first\":{},\"cmp\":\"{}\",\"second\":{},\"and\":{}}}", opnd_json(Operand::Sig(c.first), c.first_nets), pat::cmp_py(c.cmp), opnd_json(c.second, c.second_nets), c.and))
                .collect();
            let outs: Vec<String> = d.outputs.iter().map(|o| format!("{{\"sig\":\"{}\",\"copy\":{},\"const\":{},\"nets\":\"{}\"}}", name(o.sig), o.copy, o.constant, nets_s(o.nets))).collect();
            format!("{{\"type\":\"decider\",\"conds\":[{}],\"outputs\":[{}]}}", conds.join(","), outs.join(","))
        }
        Kind::Selector(s) => format!("{{\"type\":\"selector\",\"mode\":\"{s:?}\"}}"),
        _ => "{}".into(),
    }
}

fn opnd_text(o: Operand, n: Nets) -> String {
    match o {
        Operand::Sig(s) => {
            let base = name(s).trim_start_matches("signal-").to_string();
            match (n.red, n.green) {
                (true, false) => format!("{base}(r)"),
                (false, true) => format!("{base}(g)"),
                _ => base,
            }
        }
        Operand::Const(c) => c.to_string(),
    }
}

fn kind_text(k: &Kind) -> String {
    match k {
        Kind::Arith(a) => format!("arith {} {} {} -> {}", opnd_text(a.first, a.first_nets), a.op.symbol(), opnd_text(a.second, a.second_nets), opnd_text(Operand::Sig(a.out), Nets::BOTH)),
        Kind::Decider(d) => {
            let mut s = String::from("decider ");
            for (i, c) in d.conds.iter().enumerate() {
                if i > 0 {
                    s.push_str(if c.and { " & " } else { " | " });
                }
                s.push_str(&format!("{} {} {}", opnd_text(Operand::Sig(c.first), c.first_nets), c.cmp.symbol(), opnd_text(c.second, c.second_nets)));
            }
            let outs: Vec<String> = d
                .outputs
                .iter()
                .map(|o| {
                    let s = opnd_text(Operand::Sig(o.sig), Nets::BOTH);
                    if o.copy {
                        format!("{s}=copy({})", nets_s(o.nets).to_lowercase())
                    } else {
                        format!("{s}={}", o.constant)
                    }
                })
                .collect();
            s.push_str(&format!(" -> {}", outs.join(", ")));
            s
        }
        Kind::Selector(sel) => format!("selector {sel:?}"),
        _ => "?".into(),
    }
}

impl Circuit {
    fn text(&self) -> String {
        let mut parts = Vec::new();
        for (c, to_p) in &self.combs {
            let red = match c.red {
                Red::None => String::new(),
                Red::Table(i) => format!(" [red: table {{{}}}]", self.tables[i].iter().map(|(s, v)| format!("{}:{v}", name(*s).trim_start_matches("signal-"))).collect::<Vec<_>>().join(",")),
                Red::P => " [red: P]".into(),
            };
            parts.push(format!("{}{red}{}", kind_text(&c.kind), if *to_p { " => P" } else { "" }));
        }
        if self.offset != 0 {
            parts.push(format!("constant O={}", self.offset));
        }
        parts.join("; ")
    }

    fn json(&self) -> String {
        let combs: Vec<String> = self
            .combs
            .iter()
            .map(|(c, to_p)| {
                let red = match c.red {
                    Red::None => "null".to_string(),
                    Red::Table(i) => format!("[{}]", self.tables[i].iter().map(|(s, v)| format!("[\"{}\",{v}]", name(*s))).collect::<Vec<_>>().join(",")),
                    Red::P => "\"P\"".into(),
                };
                format!("{{\"kind\":{},\"red\":{red},\"to\":\"{}\"}}", kind_json(&c.kind), if *to_p { "P" } else { "OUT" })
            })
            .collect();
        format!("{{\"combs\":[{}],\"offset\":{}}}", combs.join(","), self.offset)
    }
}

// ------------------------------------------------------------------ search

struct Target {
    count: usize,
    cost: usize,
    shape: String,
    ivs: Vec<(i64, i64)>,
}

struct Found {
    circuit: Option<Circuit>,
    evals: u64,
    secs: f64,
    notes: String,
}

fn search(t: &Target, sigs: &Sigs, seed: u64, budget: f64) -> Result<Found, String> {
    let start = Instant::now();
    let p = Pat::parse(&t.shape)?;
    let n = p.leaves();
    if n == 0 || n > 3 {
        return Err(format!("{n} leaves"));
    }
    let mut rng = Rng(seed ^ hash(&t.shape));
    let tests = make_tests(&p, &t.ivs, sigs, &mut rng);
    let xs: Vec<Sig> = sigs.x[..n].to_vec();
    // Constants: the pattern's, their negations and neighbours, 0 and ±1.
    let mut consts: Vec<i32> = Vec::new();
    for c in p.consts().into_iter().chain([0, 1, -1]) {
        for v in [c, c.wrapping_neg(), c.wrapping_add(1), c.wrapping_sub(1)] {
            if !consts.contains(&v) && consts.len() < 14 {
                consts.push(v);
            }
        }
    }
    let mut lits = Vec::new();
    for i in 0..n {
        let mut seconds: Vec<(Operand, Nets)> = (0..n).filter(|&j| j != i).map(|j| g(xs[j])).collect();
        seconds.extend(consts.iter().map(|&c| k(c)));
        for sec in seconds {
            for cmp in ALL_CMP {
                lits.push(Lit { first: xs[i], first_nets: Nets::GREEN, cmp, second: sec });
            }
        }
    }
    let mut plits: Vec<Lit> = p.literals().into_iter().map(|l| lit_of(&xs, l)).collect();
    for i in 0..n {
        for j in 0..n {
            if i != j {
                for cmp in ALL_CMP {
                    let l = Lit { first: xs[i], first_nets: Nets::GREEN, cmp, second: g(xs[j]) };
                    if !plits.contains(&l) {
                        plits.push(l);
                    }
                }
            }
        }
    }
    let mut outk: Vec<i32> = vec![1];
    let mut fvals: Vec<i32> = tests.f.iter().copied().filter(|v| *v != 0).collect();
    fvals.sort_unstable();
    fvals.dedup();
    if fvals.len() <= 4 {
        outk.extend(fvals.iter().copied().filter(|v| *v != 1));
    }
    for &c in &p.consts() {
        if !outk.contains(&c) && c != 0 {
            outk.push(c);
        }
    }
    let pdnfs: Vec<Vec<Vec<Lit>>> = p.dnfs().into_iter().map(|d| d.into_iter().map(|t| t.into_iter().map(|l| lit_of(&xs, l)).collect()).collect()).collect();
    let alpha = Alpha { xs: xs.clone(), consts, lits, plits, pdnfs, outk };
    // Tables: masks giving each input a code (all inputs; each one alone).
    let mut tables: Vec<Vec<(Sig, i32)>> = vec![xs.iter().enumerate().map(|(i, &x)| (x, i as i32 + 1)).collect()];
    if n > 1 {
        for &x in &xs {
            tables.push(vec![(x, 1)]);
        }
    }
    let mut eng = Engine { tables: tables.clone(), evals: 0 };
    let mut reds: Vec<(Red, Vec<Sig>)> = vec![(Red::None, vec![])];
    for (i, tb) in tables.iter().enumerate() {
        reds.push((Red::Table(i), tb.iter().map(|x| x.0).collect()));
    }
    let mut best: Option<Circuit> = None;
    let consider = |c: Circuit, best: &mut Option<Circuit>| {
        if best.as_ref().is_none_or(|b| c.key() < b.key()) {
            *best = Some(c);
        }
    };
    let single = |cand: &Cand| Circuit { combs: vec![(cand.clone(), false)], tables: tables.clone(), offset: 0, depth: 1 };
    let mut notes = Vec::new();

    // A and B: one or two combinators on the output, plus an optional constant.
    let a_cands = gen_single(&alpha, sigs, sigs.o, &reds, false, n <= 2);
    let a_sigs = eng.signatures(&a_cands, &tests.bus, None, sigs.o);
    let mut by_sig: HashMap<&[i32], usize> = HashMap::new();
    let mut by_quick: HashMap<&[i32], Vec<usize>> = HashMap::new();
    for (i, s) in a_sigs.iter().enumerate() {
        if let Some(s) = s {
            by_sig.entry(&s[..]).or_insert(i);
            let q = by_quick.entry(&s[..QUICK.min(s.len())]).or_default();
            if q.len() < 4 {
                q.push(i);
            }
        }
    }
    notes.push(format!("A {}", a_cands.len()));
    for (i, s) in a_sigs.iter().enumerate() {
        let Some(s) = s else { continue };
        if *s == tests.f {
            consider(single(&a_cands[i]), &mut best);
        }
        let need: Vec<i32> = tests.f.iter().zip(s).map(|(f, v)| f.wrapping_sub(*v)).collect();
        if need.iter().all(|v| *v == need[0]) {
            let mut c = single(&a_cands[i]);
            c.offset = need[0];
            consider(c, &mut best);
        }
        if let Some(&j) = by_sig.get(&need[..]) {
            let mut c = single(&a_cands[i]);
            c.combs.push((a_cands[j].clone(), false));
            consider(c, &mut best);
        }
    }
    let within = |b: &Option<Circuit>, n: usize| b.as_ref().is_some_and(|c| c.combinators() <= n);

    // S and C: a combinator onto P, one reading the bus and P (plus one of kind A).
    if !within(&best, 2) && t.cost >= 3 && start.elapsed().as_secs_f64() < budget {
        let p_cands = gen_single(&alpha, sigs, sigs.t, &reds, true, false);
        // Distinct, noise-free P contents (first candidate of each, at most MAX_P).
        let hashes = eng.content_hashes(&p_cands, &tests.bus, &sigs.noise);
        let mut seen: HashMap<u64, usize> = HashMap::new();
        for (i, h) in hashes.into_iter().enumerate() {
            if let Some(h) = h {
                seen.entry(h).or_insert(i);
            }
        }
        let mut firsts: Vec<usize> = seen.into_values().collect();
        firsts.sort_unstable();
        firsts.truncate(MAX_P);
        let chosen: Vec<Cand> = firsts.iter().map(|&i| p_cands[i].clone()).collect();
        let ps: Vec<(Vec<Vec<(Sig, i32)>>, usize)> = eng.contents(&chosen, &tests.bus).into_iter().zip(firsts.iter().copied()).collect();
        notes.push(format!("P {} distinct of {}", ps.len(), p_cands.len()));
        let mut rsigs: Vec<Sig> = vec![sigs.t];
        rsigs.extend(xs.iter().copied());
        let c2 = gen_single(&alpha, sigs, sigs.o, &[(Red::P, rsigs)], false, false);
        notes.push(format!("S {}", c2.len()));
        let nq = QUICK.min(tests.bus.len());
        let quick: Vec<Bus> = tests.bus[..nq].to_vec();
        let fq = &tests.f[..nq];
        for (pi, (content, src)) in ps.iter().enumerate() {
            if start.elapsed().as_secs_f64() > budget {
                notes.push(format!("budget hit after {pi} P contents"));
                break;
            }
            let qs = eng.signatures(&c2, &quick, Some(&content[..nq]), sigs.o);
            for (j, s) in qs.iter().enumerate() {
                let Some(s) = s else { continue };
                let exact = s == fq;
                let need: Vec<i32> = fq.iter().zip(s).map(|(f, v)| f.wrapping_sub(*v)).collect();
                let partner = if !exact && !within(&best, 3) { by_quick.get(&need[..]).cloned() } else { None };
                if !exact && partner.is_none() {
                    continue;
                }
                let full = eng.signatures(std::slice::from_ref(&c2[j]), &tests.bus, Some(content), sigs.o).pop().flatten();
                let Some(full) = full else { continue };
                let serial = Circuit { combs: vec![(p_cands[*src].clone(), true), (c2[j].clone(), false)], tables: tables.clone(), offset: 0, depth: 2 };
                if full == tests.f {
                    consider(serial.clone(), &mut best);
                }
                for &a in partner.iter().flatten() {
                    let sa = a_sigs[a].as_ref().unwrap();
                    if full.iter().zip(sa).zip(&tests.f).all(|((x, y), f)| x.wrapping_add(*y) == *f) {
                        let mut c = serial.clone();
                        c.combs.push((a_cands[a].clone(), false));
                        consider(c, &mut best);
                    }
                }
            }
            if within(&best, 2) {
                break;
            }
        }
    }
    Ok(Found { circuit: best, evals: eng.evals, secs: start.elapsed().as_secs_f64(), notes: notes.join(", ") })
}

fn hash(s: &str) -> u64 {
    s.bytes().fold(0xcbf2_9ce4_8422_2325u64, |h, b| (h ^ b as u64).wrapping_mul(0x100_0000_01b3))
}

// ------------------------------------------------------------------ main

fn read_targets(path: &str) -> Vec<Target> {
    let text = std::fs::read_to_string(path).unwrap_or_else(|e| panic!("{path}: {e}"));
    let mut out = Vec::new();
    for line in text.lines() {
        let f: Vec<&str> = line.split('\t').collect();
        if f.len() < 4 {
            continue;
        }
        let ivs = if f[3] == "-" {
            vec![]
        } else {
            f[3].split(',')
                .map(|l| {
                    let p: Vec<&str> = l.split(':').collect();
                    (p[1].parse().unwrap(), p[2].parse().unwrap())
                })
                .collect()
        };
        out.push(Target { count: f[0].parse().unwrap(), cost: f[1].parse().unwrap(), shape: f[2].to_string(), ivs });
    }
    out
}

fn main() {
    let args: Vec<String> = std::env::args().collect();
    let get = |flag: &str| args.iter().position(|a| a == flag).and_then(|i| args.get(i + 1)).cloned();
    match args.get(1).map(|s| s.as_str()) {
        Some("eval") => {
            let p = Pat::parse(&args[2]).expect("pattern");
            let x: Vec<i32> = args[3..].iter().map(|a| a.parse().unwrap()).collect();
            println!("{}", p.eval(&x));
        }
        Some("search") => {
            let targets = read_targets(&get("--targets").expect("--targets FILE"));
            let top: usize = get("--top").map_or(40, |v| v.parse().unwrap());
            let seed: u64 = get("--seed").map_or(1, |v| v.parse().unwrap());
            let min_excess: usize = get("--min-excess").map_or(4, |v| v.parse().unwrap());
            let budget: f64 = get("--budget").map_or(60.0, |v| v.parse().unwrap());
            let out = get("--out");
            let sigs = Sigs::new();
            // Targets by what they cost beyond one combinator each, at most 3 leaves.
            let mut ts: Vec<&Target> = targets.iter().filter(|t| t.cost > t.count && t.cost - t.count >= min_excess && t.ivs.len() <= 3).collect();
            ts.sort_by_key(|t| (std::cmp::Reverse(t.cost - t.count), t.shape.clone()));
            ts.truncate(top);
            let mut lines = Vec::new();
            let (mut today, mut after, mut patterns, mut improved) = (0usize, 0usize, 0usize, 0usize);
            for t in ts {
                let avg = t.cost as f64 / t.count as f64;
                match search(t, &sigs, seed, budget) {
                    Err(e) => eprintln!("skip {}: {e}", t.shape),
                    Ok(f) => {
                        patterns += 1;
                        today += t.cost;
                        let (n, d, consts) = f.circuit.as_ref().map_or((usize::MAX, 0, 0), |c| (c.combinators(), c.depth, c.constants()));
                        let better = (n as f64) < avg - 1e-9;
                        if better {
                            improved += 1;
                            after += n * t.count;
                        } else {
                            after += t.cost;
                        }
                        println!(
                            "{:>4}x avg {:.2} -> {} (depth {d}, {consts} constants)  {}   [{:.1}s, {} evals; {}]",
                            t.count,
                            avg,
                            if n == usize::MAX { "none ≤3".into() } else { n.to_string() },
                            t.shape,
                            f.secs,
                            f.evals,
                            f.notes
                        );
                        if let Some(c) = &f.circuit {
                            println!("        {}", c.text());
                            lines.push(format!(
                                "{{\"shape\":\"{}\",\"leaves\":[{}],\"count\":{},\"today\":{},\"combinators\":{n},\"constants\":{consts},\"depth\":{d},\"better\":{better},\"text\":\"{}\",\"circuit\":{}}}",
                                t.shape,
                                t.ivs.iter().map(|(a, b)| format!("[{a},{b}]")).collect::<Vec<_>>().join(","),
                                t.count,
                                t.cost,
                                c.text().replace('"', "'"),
                                c.json()
                            ));
                        }
                    }
                }
            }
            println!("{patterns} patterns: {improved} improved; their combinators {today} -> {after} (if every occurrence took the winner)");
            if let Some(o) = out {
                let mut f = std::fs::File::create(&o).expect("--out");
                for l in lines {
                    writeln!(f, "{l}").unwrap();
                }
            }
        }
        _ => {
            eprintln!("usage: superopt search --targets FILE [--top N] [--seed S] [--out RULES.jsonl] [--min-excess E] [--budget SECONDS]\n       superopt eval 'SHAPE' X0 [X1 [X2]]");
            std::process::exit(2);
        }
    }
}
