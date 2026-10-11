//! Blocks that run every tick: a balanced pipeline reading inputs directly, with operands
//! delayed to their consumer's iteration ([`Delays`]), registers enabled by the start-up
//! signals ([`Warm`]), and combinational outputs read straight off the pipeline.
//!
//! Delays: a value needed `d` ticks after it is computed is either on the bus under a new
//! signal (a chain of `s + 0` delays, one combinator per value per tick) or, with carry
//! wires, under its own signal on carry wire `d`: a private red wire holding the bus as it
//! was `d` ticks ago (one decider copies the carried signals off the bus onto wire 1, then
//! one `each + 0` per wire). A combinator whose delayed operands all have the same delay
//! reads the bus on green and that carry wire on red, so the delay costs it nothing;
//! anything else that needs a value `d` ticks old gets a tap (`s + 0` from wire `d - 1`
//! onto the bus). Each block is built with 0, 1, 2, … carry wires and both schedules from
//! [`crate::pipeline`], keeping the smallest.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use ticky_factorio::*;
use ticky_syntax::Diag;

use super::registers::{accumulator, Writer};
use super::*;
use crate::fuse::{is_true, LoadVal, WriterPlan};
use crate::ir::{Graph, Lit, Op, V};
use crate::program::Program;

/// A block that runs every tick: logic is a balanced pipeline reading inputs directly.
/// Returns where each combinational output (`comb`) of the block can be read (and the
/// carry wire to read it from on red, for those not on the bus).
#[allow(clippy::too_many_arguments)]
pub(super) fn pipelined_block(
    cg: &mut Cg,
    p: &Program,
    bi: usize,
    b: &crate::program::Block,
    pipe: &crate::pipeline::Pipe,
    shared: &Shared,
    live: &[bool],
    comb: &std::collections::HashSet<usize>,
) -> Result<Built, Diag> {
    let first = cg.net.entities.len();
    let mut best: Option<(usize, Cg, Built)> = None;
    let mut err = None;
    for (ti, tau) in pipe.taus.iter().enumerate() {
        for inline in [false, true] {
            for stages in 0.. {
                let mut trial = cg.clone();
                let shape = Shape { tau, stages, inline };
                let used = match build(&mut trial, p, bi, b, pipe, &shape, shared, live, comb) {
                    Ok((r, used)) => {
                        let n = trial.combinators_since(first);
                        if std::env::var_os("TICKY_DUMP_PIPE").is_some() {
                            eprintln!("block {}: schedule {ti}, inline {inline}, {stages} carry wires: {n} combinators ({used} built)", bi + 1);
                        }
                        if best.as_ref().is_none_or(|(m, _, _)| n < *m) {
                            best = Some((n, trial, r));
                        }
                        used
                    }
                    Err(e) => {
                        err.get_or_insert(e);
                        0
                    }
                };
                // More carry wires than the last build used would build the same again.
                if used < stages || stages > pipe.latency as usize + 1 {
                    break;
                }
            }
        }
    }
    let (_, built, r) = best.ok_or_else(|| err.unwrap())?;
    *cg = built;
    Ok(r)
}

/// Where combinational outputs are (on the bus, or on a carry wire by net), and how many
/// ticks they come after the pipeline's offset 0.
type Built = (HashMap<usize, Ref>, HashMap<usize, usize>, u32);

/// One way to build a block.
struct Shape<'a> {
    /// The schedule (one of [`crate::pipeline::Pipe::taus`]).
    tau: &'a [Option<i32>],
    /// How many carry wires may be built.
    stages: usize,
    /// Whether conditions used only to choose constants are tested by the select's deciders
    /// themselves (reading their operands a tick later) rather than built.
    inline: bool,
}

/// Builds the block. Also returns how many carry wires it built.
#[allow(clippy::too_many_arguments)]
fn build(
    cg: &mut Cg,
    p: &Program,
    bi: usize,
    b: &crate::program::Block,
    pipe: &crate::pipeline::Pipe,
    shape: &Shape,
    shared: &Shared,
    live: &[bool],
    comb: &std::collections::HashSet<usize>,
) -> Result<(Built, usize), Diag> {
    let what = format!("block {}", bi + 1);
    let g = &b.graph;
    let (tau, stages) = (shape.tau, shape.stages);
    let owned: Vec<usize> = (0..p.states.len()).filter(|&si| p.states[si].owner == Some(bi) && live[si]).collect();
    let registers = owned.iter().any(|si| !comb.contains(si));
    // Commit only once the pipeline holds values computed from inputs read after the start.
    let (en, en_prefix) = if registers {
        let en = cg.warm_en(pipe.latency as usize + 1)?;
        (en, cg.warm_cond(pipe.latency as usize))
    } else {
        (cg.rp, vec![c(cg.rp, CmpOp::Ne, 0)])
    };
    let src_ref: Vec<Ref> = b.srcs.iter().map(|k| shared.raw(p, *k).0).collect();

    // Node signals, then combinators with operands delayed to their consumer's iteration.
    let plans: Vec<&(usize, WriterPlan)> = b.plans.iter().filter(|(si, _)| live[*si]).collect();
    let accs: Vec<&(usize, crate::pipeline::Acc)> = pipe.accs.iter().filter(|(si, _)| live[*si]).collect();
    let acc_conds = |a: &crate::pipeline::Acc| -> Vec<V> {
        a.consts.iter().flat_map(|(d, _)| crate::ir::dnf_operands(d)).chain(crate::ir::dnf_operands(&a.otherwise)).collect()
    };
    let mut roots: Vec<V> = plans.iter().flat_map(|(_, p)| p.operands()).collect();
    for (_, a) in &accs {
        roots.push(a.w);
        roots.extend(acc_conds(a));
    }
    let nodes = g.reachable(&roots);
    let inline = if shape.inline { inline_conds(g, &nodes, &roots) } else { HashSet::new() };
    let mut node_ref: HashMap<V, Ref> = HashMap::new();
    for &v in &nodes {
        // Inlined conditions aren't built; parts of a sum write the sum's signal.
        if inline.contains(&v) || pipe.fold.get(&v).is_some_and(|&(sum, _)| sum != v) {
            continue;
        }
        match g.op(v) {
            Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) | Op::Sel(_) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_) | Op::AGet(..) | Op::BDot(..) => {
                node_ref.insert(v, Ref::Op(Operand::Sig(cg.alloc()?)));
            }
            Op::BConst(_) | Op::Bun(_) | Op::BMux { .. } | Op::BDec(_) | Op::BSelect(..) | Op::BSelectAt(..) | Op::BSel(..) => {
                node_ref.insert(v, Ref::Bun(cg.bnew()));
            }
            _ => {}
        }
    }
    let mut dl = Delays {
        g,
        tau,
        node_ref: &node_ref,
        src_ref: &src_ref,
        what: &what,
        stages,
        carry: Vec::new(),
        first: None,
        carried: HashSet::new(),
        bus: HashMap::new(),
    };
    let as_sig = |o: Operand| match o {
        Operand::Sig(s) => s,
        Operand::Const(_) => unreachable!("constant where a signal is required"),
    };
    // A condition `x op y` on operands read by `Delays::read`.
    let cond = |x: (Operand, Nets), op: CmpOp, y: (Operand, Nets)| Cond { first: as_sig(x.0), first_nets: x.1, second: y.0, second_nets: y.1, cmp: op, and: true };
    for &v in &nodes {
        // A sum on the wire is its parts' outputs: nothing to build. Each part writes its
        // value times `m` onto the sum's signal.
        if pipe.transparent.contains(&v) {
            continue;
        }
        let (out_ref, m) = match (pipe.fold.get(&v), node_ref.get(&v)) {
            (Some(&(sum, m)), _) => (node_ref[&sum], m),
            (None, Some(&r)) => (r, 1),
            (None, None) => continue,
        };
        if matches!(g.op(v), Op::BConst(_)) {
            cg.emit_bundle(g, v, out_ref.bun(), &|_| unreachable!(), &|_| None, &|_| false, &what);
            continue;
        }
        let t = tau[v as usize].unwrap() - 1;
        if let Op::Bun(_) | Op::BMux { .. } | Op::BDec(_) | Op::BSelect(..) | Op::BSelectAt(..) | Op::BSel(..) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_) | Op::AGet(..) | Op::BDot(..) = g.op(v) {
            // Operands as of this node's input tick (on the bus: bundle combinators read a
            // bundle on red), then the combinators.
            let mut ops: HashMap<V, Ref> = HashMap::new();
            for u in g.operands(v) {
                let r = dl.at(cg, u, t)?;
                ops.insert(u, r);
            }
            let look = |u: V| ops[&u];
            match out_ref {
                Ref::Bun(o) => cg.emit_bundle(g, v, o, &look, &|_| None, &|_| false, &what),
                r => cg.emit_from_bundle(g, v, r.sig(), m, None, &look, &what),
            }
            continue;
        }
        let out = out_ref.sig();
        match g.op(v).clone() {
            Op::Ar(op, a, bb) => {
                let (mut r, red) = dl.read(cg, &[(a, t), (bb, t)])?;
                // Times `m` (see `pipeline::wire_sums`): `-(x - y)` is `y - x`, `-(x / k)` is
                // `x / -k`, constant factors multiply.
                match (op, r[0].0, r[1].0) {
                    _ if m == 1 => {}
                    (ArOp::Sub, ..) if m == -1 => r.swap(0, 1),
                    (ArOp::Mul, _, Operand::Const(k)) | (ArOp::Div, _, Operand::Const(k)) => r[1].0 = Operand::Const(k * m),
                    (ArOp::Mul, Operand::Const(k), _) => r[0].0 = Operand::Const(k * m),
                    _ => unreachable!("not a wire sum part"),
                }
                let k = Kind::Arith(Arith { first: r[0].0, first_nets: r[0].1, second: r[1].0, second_nets: r[1].1, op, out });
                let id = cg.core(k, format!("{what}: arithmetic"));
                dl.attach(cg, id, red);
            }
            Op::Cmp(op, a, bb) => {
                let (r, red) = dl.read(cg, &[(a, t), (bb, t)])?;
                let id = cg.core(dec_const(vec![cond(r[0], op, r[1])], out, m), format!("{what}: comparison"));
                dl.attach(cg, id, red);
            }
            Op::Mux { .. } | Op::Sel(_) => {
                let arms: Vec<(V, V)> = match g.op(v) {
                    Op::Mux { t, f, a, b } => vec![(*t, *a), (*f, *b)],
                    Op::Sel(arms) => arms.clone(),
                    _ => unreachable!(),
                };
                for (cv, val) in arms {
                    // An arm worth 0 adds nothing (and its condition isn't computed).
                    if g.as_const(val) == Some(0) {
                        continue;
                    }
                    if inline.contains(&cv) {
                        // The condition's own literals, as of the select's input tick.
                        let Some(k) = g.as_const(val) else { unreachable!("inlined conditions choose constants") };
                        let d = cond_dnf(g, cv);
                        let ops: Vec<(V, i32)> = d.iter().flatten().flat_map(|l| [(l.a, t), (l.b, t)]).collect();
                        let (r, red) = dl.read(cg, &ops)?;
                        let terms = dl_terms(&d, &r, &cond);
                        let id = cg.core(dec_const(distribute(&[], &terms), out, k * m), format!("{what}: select"));
                        dl.attach(cg, id, red);
                        continue;
                    }
                    let (r, red) = dl.read(cg, &[(cv, t), (val, t)])?;
                    let id = match r[1].0 {
                        Operand::Const(0) => continue,
                        Operand::Const(k) => {
                            let ne = cond(r[0], CmpOp::Ne, (Operand::Const(0), Nets::BOTH));
                            cg.core(dec_const(vec![ne], out, k * m), format!("{what}: select"))
                        }
                        Operand::Sig(_) => {
                            let k = Kind::Arith(Arith { first: r[1].0, first_nets: r[1].1, second: r[0].0, second_nets: r[0].1, op: ArOp::Mul, out });
                            cg.core(k, format!("{what}: select"))
                        }
                    };
                    dl.attach(cg, id, red);
                }
            }
            Op::Dec(arms) => {
                for (d, k) in arms {
                    let ops: Vec<(V, i32)> = d.iter().flatten().flat_map(|l| [(l.a, t), (l.b, t)]).collect();
                    let (r, red) = dl.read(cg, &ops)?;
                    let terms = dl_terms(&d, &r, &cond);
                    let id = cg.core(dec_const(distribute(&[], &terms), out, k * m), format!("{what}: condition"));
                    dl.attach(cg, id, red);
                }
            }
            _ => unreachable!("not a scalar operation"),
        }
    }

    // Loads read values at offset 0; enable deciders read their conditions one tick early.
    let mut ready: HashMap<(V, i32), Ref> = HashMap::new();
    for (_, plan) in &plans {
        for l in &plan.loads {
            let guard_at = if l.direct || is_true(&l.guard) { 0 } else { -1 };
            for v in crate::ir::dnf_operands(&l.guard) {
                ready.insert((v, guard_at), Ref::Op(dl.at(cg, v, guard_at)?.op()));
            }
            if let LoadVal::Node(v) = l.val {
                ready.insert((v, 0), dl.at(cg, v, 0)?);
            }
        }
        if let Some(k) = &plan.keep {
            for v in crate::ir::dnf_operands(k) {
                ready.insert((v, 0), Ref::Op(dl.at(cg, v, 0)?.op()));
            }
        }
    }
    let mut acc_w: Vec<(usize, Operand)> = Vec::new();
    for (si, a) in &accs {
        acc_w.push((*si, dl.at(cg, a.w, -1)?.op()));
        for v in acc_conds(a) {
            ready.insert((v, 0), Ref::Op(dl.at(cg, v, 0)?.op()));
        }
    }
    // Combinational outputs: the value at offset 0, or one tick later when other states of
    // the block go through registers (whose outputs show values a tick later), so that all
    // outputs of an iteration change together.
    // Conditions checked on the commit tick (direct loads) also push outputs a tick later.
    let late = registers || plans.iter().any(|(si, p)| comb.contains(si) && p.loads.iter().any(|l| l.direct));
    let o = if late { 1 } else { 0 };
    let mut direct: HashMap<usize, Ref> = HashMap::new();
    let mut direct_red: HashMap<usize, usize> = HashMap::new();
    for (si, plan) in &plans {
        if !comb.contains(si) {
            continue;
        }
        let r = match (plan.loads.as_slice(), plan.loads.first().map(|l| is_true(&l.guard))) {
            ([l], Some(true)) => match l.val {
                LoadVal::Const(k) => Ref::Op(Operand::Const(k)),
                // The output port can read a carry wire.
                LoadVal::Node(v) => match dl.delayed(v, o) {
                    Some((s, d)) if d as usize <= stages => {
                        direct_red.insert(*si, dl.wire(cg, s, d as usize));
                        Ref::Op(Operand::Sig(s))
                    }
                    _ => dl.at(cg, v, o)?,
                },
            },
            _ => {
                // Constants under (mutually exclusive) conditions: one decider each.
                let out = cg.alloc()?;
                for l in &plan.loads {
                    let LoadVal::Const(k) = l.val else { unreachable!("checked by combinational()") };
                    if k == 0 {
                        continue;
                    }
                    let ops: Vec<(V, i32)> = l.guard.iter().flatten().flat_map(|lit| [(lit.a, o - 1), (lit.b, o - 1)]).collect();
                    let (r, red) = dl.read(cg, &ops)?;
                    let terms = dl_terms(&l.guard, &r, &cond);
                    let id = cg.core(dec_const(distribute(&[], &terms), out, k), format!("{what}: {}", p.states[*si].display_name()));
                    dl.attach(cg, id, red);
                }
                Ref::Op(Operand::Sig(out))
            }
        };
        direct.insert(*si, r);
    }
    let used = dl.carry.len();
    let val = |v: V| ready[&(v, 0)];
    let lit_at = |l: &Lit, when: i32| Cond { second: ready[&(l.b, when)].op(), ..c(ready[&(l.a, when)].sig(), l.op, 0) };
    let lit = |l: &Lit| lit_at(l, 0);
    let lit_eg = |l: &Lit| lit_at(l, -1);
    for (si, s) in p.states.iter().enumerate() {
        if s.owner != Some(bi) || !live[si] {
            continue;
        }
        if comb.contains(&si) {
            continue;
        }
        let name = format!("state {}", s.display_name());
        if let Some((_, w)) = acc_w.iter().find(|(a, _)| *a == si) {
            let acc = &accs.iter().find(|(a, _)| *a == si).unwrap().1;
            accumulator(cg, shared.state_sig[&si], s.init, *w, acc, en, &lit, &name);
            continue;
        }
        let ws: Vec<Writer> = plans
            .iter()
            .filter(|(w, _)| *w == si)
            .map(|(_, plan)| Writer { en, prefix: en_prefix.clone(), plan, val: &val, lit: &lit, lit_eg: &lit_eg, stage: Vec::new() })
            .collect();
        match shared.state(si) {
            Ref::Bun(x) => cg.bregister(x, &s.binit, &ws, &name)?,
            r => cg.register(r.sig(), s.init, &ws, &name)?,
        }
    }
    Ok(((direct, direct_red, if registers { 1 } else { o as u32 }), used))
}

/// Conditions (comparisons, or one-arm conditions worth 1) used only to choose nonzero
/// constants in selects: each such arm's decider can test the condition itself.
fn inline_conds(g: &Graph, nodes: &[V], roots: &[V]) -> HashSet<V> {
    let arms = |m: V| -> Option<Vec<(V, V)>> {
        match g.op(m) {
            Op::Mux { t, f, a, b } => Some(vec![(*t, *a), (*f, *b)]),
            Op::Sel(arms) => Some(arms.clone()),
            _ => None,
        }
    };
    let mut users: HashMap<V, Vec<V>> = HashMap::new();
    for &v in nodes {
        for u in g.operands(v) {
            users.entry(u).or_default().push(v);
        }
    }
    nodes
        .iter()
        .copied()
        .filter(|&c| {
            let boolean = match g.op(c) {
                Op::Cmp(_, a, _) => g.as_const(*a).is_none(),
                Op::Dec(arms) => arms.len() == 1 && arms[0].1 == 1,
                _ => false,
            };
            boolean
                && !roots.contains(&c)
                && users.get(&c).is_some_and(|us| {
                    us.iter().all(|&m| {
                        arms(m).is_some_and(|arms| {
                            arms.iter().all(|&(cv, x)| match g.as_const(x) {
                                Some(0) => true,
                                _ if x == c => false,
                                Some(_) => true,
                                None => cv != c,
                            })
                        })
                    })
                })
        })
        .collect()
}

/// An inlinable condition as a DNF of literals.
fn cond_dnf(g: &Graph, c: V) -> crate::ir::Dnf {
    match g.op(c) {
        Op::Cmp(op, a, b) => vec![vec![Lit { a: *a, op: *op, b: *b }]],
        Op::Dec(arms) => arms[0].0.clone(),
        _ => unreachable!("not a condition"),
    }
}

/// Decider conditions for `d`, whose literals' operands (`a`, `b` of each, in order) were
/// read as `r`.
fn dl_terms(d: &crate::ir::Dnf, r: &[(Operand, Nets)], cond: &dyn Fn((Operand, Nets), CmpOp, (Operand, Nets)) -> Cond) -> CDnf {
    let mut r = r.iter();
    d.iter().map(|term| term.iter().map(|l| cond(*r.next().unwrap(), l.op, *r.next().unwrap())).collect()).collect()
}

/// Operands as read by one combinator (each with the wires to read it on), and the carry
/// wire to connect to its red input.
type Reads = (Vec<(Operand, Nets)>, Option<usize>);

/// Operands delayed to their consumer's iteration (see the module docs).
struct Delays<'a> {
    g: &'a Graph,
    tau: &'a [Option<i32>],
    node_ref: &'a HashMap<V, Ref>,
    src_ref: &'a [Ref],
    what: &'a str,
    /// How many carry wires may be built.
    stages: usize,
    /// Nets of the carry wires built so far: `carry[d - 1]` holds the bus `d` ticks ago.
    carry: Vec<usize>,
    /// The decider copying signals off the bus onto the first carry wire.
    first: Option<EntId>,
    /// Signals it copies.
    carried: HashSet<Sig>,
    /// Delayed copies on the bus, by value and offset.
    bus: HashMap<(V, i32), Ref>,
}

impl Delays<'_> {
    /// Where `u` is computed (or a constant).
    fn base(&self, u: V) -> Ref {
        match *self.g.op(u) {
            Op::Const(k) => Ref::Op(Operand::Const(k)),
            Op::Src(s) => self.src_ref[s as usize],
            _ => self.node_ref[&u],
        }
    }

    /// `u`'s signal and how many ticks old it is wanted at offset `at`, if it's a delayed
    /// scalar (one that could come from a carry wire).
    fn delayed(&self, u: V, at: i32) -> Option<(Sig, i32)> {
        match (self.g.op(u), self.base(u)) {
            (Op::Const(_) | Op::BConst(_), _) => None,
            (_, Ref::Op(Operand::Sig(s))) => {
                let d = at - self.tau[u as usize].expect("timed node");
                (d >= 1).then_some((s, d))
            }
            _ => None,
        }
    }

    /// The net of carry wire `d` (building wires up to it), with signal `s` on it.
    fn wire(&mut self, cg: &mut Cg, s: Sig, d: usize) -> usize {
        let what = self.what;
        let first = match self.first {
            Some(id) => id,
            None => {
                // A condition that always holds, so that the wires follow the bus even while
                // RUN is off, like delay chains.
                let always = Cond { first_nets: Nets::GREEN, ..c(cg.run, CmpOp::Ge, i32::MIN) };
                let id = cg.loose(dec(vec![always], Vec::new()), format!("{what}: carry 1"));
                cg.on_bus_in(id);
                cg.nets.push(NetSpec { red: true, members: vec![(id, Conn::OutRed)] });
                self.carry.push(cg.nets.len() - 1);
                self.first = Some(id);
                id
            }
        };
        if self.carried.insert(s) {
            let Kind::Decider(dc) = &mut cg.net.entities[first].kind else { unreachable!() };
            dc.outputs.push(DOut { sig: s, copy: true, constant: 1, nets: Nets::GREEN });
        }
        while self.carry.len() < d {
            let each = cg.each;
            let k = Kind::Arith(Arith { first: Operand::Sig(each), first_nets: Nets::RED, second: Operand::Const(0), second_nets: Nets::BOTH, op: ArOp::Add, out: each });
            let id = cg.loose(k, format!("{what}: carry {}", self.carry.len() + 1));
            let prev = *self.carry.last().unwrap();
            cg.nets[prev].members.push((id, Conn::InRed));
            cg.nets.push(NetSpec { red: true, members: vec![(id, Conn::OutRed)] });
            self.carry.push(cg.nets.len() - 1);
        }
        self.carry[d - 1]
    }

    /// The value of `u` for the current iteration on the bus at offset `at`: a delayed copy
    /// tapped off a carry wire, or a delay chain.
    fn at(&mut self, cg: &mut Cg, u: V, at: i32) -> Result<Ref, Diag> {
        let base = match *self.g.op(u) {
            Op::Const(k) => return Ok(Ref::Op(Operand::Const(k))),
            Op::BConst(_) => return Ok(self.node_ref[&u]), // constant: no timing
            _ => self.base(u),
        };
        let t = self.tau[u as usize].expect("timed node");
        assert!(t <= at, "pipeline schedule: value needed before it exists");
        if t == at {
            return Ok(base);
        }
        if let Some(r) = self.bus.get(&(u, at)) {
            return Ok(*r);
        }
        let what = self.what;
        let r = match (self.delayed(u, at), base) {
            (Some((s, d)), _) if d >= 2 && d as usize - 1 <= self.stages => {
                let net = self.wire(cg, s, d as usize - 1);
                let o = cg.alloc()?;
                let k = Kind::Arith(Arith { first: Operand::Sig(s), first_nets: Nets::RED, second: Operand::Const(0), second_nets: Nets::BOTH, op: ArOp::Add, out: o });
                let id = cg.loose(k, format!("{what}: delay"));
                cg.nets[net].members.push((id, Conn::InRed));
                cg.nets[0].members.push((id, Conn::OutGreen));
                Ref::Op(Operand::Sig(o))
            }
            (_, Ref::Bun(_)) => {
                let Ref::Bun(prev) = self.at(cg, u, at - 1)? else { unreachable!() };
                let next = cg.bnew();
                let each = cg.each;
                let id = cg.loose(arith(Operand::Sig(each), ArOp::Add, Operand::Const(0), each), format!("{what}: delay"));
                cg.bread(prev, id, false);
                cg.bprod(next, id);
                Ref::Bun(next)
            }
            _ => {
                let prev = self.at(cg, u, at - 1)?;
                let s = cg.alloc()?;
                cg.core(arith(prev.op(), ArOp::Add, Operand::Const(0), s), format!("{what}: delay"));
                Ref::Op(Operand::Sig(s))
            }
        };
        self.bus.insert((u, at), r);
        Ok(r)
    }

    /// Operands `(value, offset)` of one combinator that reads scalars by name. The delay
    /// most of them share comes from a carry wire on red, if there's one that far; the rest
    /// come from the bus on green. Returns each operand with the wires to read it on, and
    /// the carry wire to connect to the combinator's red input ([`Delays::attach`]).
    fn read(&mut self, cg: &mut Cg, ops: &[(V, i32)]) -> Result<Reads, Diag> {
        let mut by_delay: BTreeMap<i32, BTreeSet<V>> = BTreeMap::new();
        for &(u, at) in ops {
            if let Some((_, d)) = self.delayed(u, at) {
                if d as usize <= self.stages {
                    by_delay.entry(d).or_default().insert(u);
                }
            }
        }
        let pick = by_delay.iter().max_by_key(|(d, us)| (us.len(), **d)).map(|(d, _)| *d);
        let mut out = Vec::new();
        let mut red = None;
        for &(u, at) in ops {
            match self.delayed(u, at) {
                Some((s, d)) if Some(d) == pick => {
                    red = Some(self.wire(cg, s, d as usize));
                    out.push((Operand::Sig(s), Nets::RED));
                }
                _ => {
                    let o = self.at(cg, u, at)?.op();
                    out.push((o, if pick.is_some() { Nets::GREEN } else { Nets::BOTH }));
                }
            }
        }
        Ok((out, red))
    }

    /// Connects a combinator built from [`Delays::read`] operands to its carry wire.
    fn attach(&self, cg: &mut Cg, id: EntId, red: Option<usize>) {
        if let Some(n) = red {
            cg.nets[n].members.push((id, Conn::InRed));
        }
    }
}

/// The start-up signals of every-tick blocks: an enable that turns on `n` ticks after RP
/// does (so registers commit only once the pipeline holds values computed from inputs read
/// after the start), and the condition one tick earlier. Either a chain of deciders (one per
/// tick, shared by all blocks) or, when that's cheaper, a counter W that the RUN switch
/// feeds +1 like a block clock, saturating, with one decider per enable.
#[derive(Clone, Default)]
pub(super) struct Warm {
    /// Chain: `chain[i]` is 1 from `i + 1` ticks after RP.
    chain: Vec<Sig>,
    /// Counter: its signal and the largest threshold read (it stops at that + 1).
    counter: Option<(Sig, i32)>,
    built: bool,
    /// Counter: enable signals by delay.
    en: HashMap<usize, Sig>,
}

/// Picks the start-up signals for the program: returns the counter's signal and its cap if
/// that's cheaper than the chain (the caller puts the signal on the RUN switch with +1).
pub(super) fn plan_warm(cg: &mut Cg, p: &Program, live: &[bool], comb: &HashSet<usize>) -> Result<Option<Sig>, Diag> {
    // The pipelines' latencies, for blocks with registers.
    let mut lat = BTreeSet::new();
    for (bi, b) in p.blocks.iter().enumerate() {
        let Some(pipe) = &b.pipe else { continue };
        if (0..p.states.len()).any(|si| p.states[si].owner == Some(bi) && live[si] && !comb.contains(&si)) {
            lat.insert(pipe.latency as i32);
        }
    }
    let Some(&max) = lat.last() else { return Ok(None) };
    // Chain: max + 1 deciders. Counter: two, and one enable per latency.
    if 2 + lat.len() as i32 >= max + 1 {
        return Ok(None);
    }
    let w = cg.alloc()?;
    cg.warm.counter = Some((w, max + 1));
    Ok(Some(w))
}

impl Cg {
    /// A 0/1 signal that turns on `n` ticks (n ≥ 1) after RP does.
    fn warm_en(&mut self, n: usize) -> Result<Sig, Diag> {
        let Some((w, cap)) = self.warm.counter else {
            while self.warm.chain.len() < n {
                let prev = self.warm.chain.last().copied().unwrap_or(self.rp);
                let s = self.alloc()?;
                self.core(dec_const(vec![c(prev, CmpOp::Ne, 0)], s, 1), format!("control: start-up delay {}", self.warm.chain.len() + 1));
                self.warm.chain.push(s);
            }
            return Ok(self.warm.chain[n - 1]);
        };
        if !self.warm.built {
            // W reads its own output + 1 (from the RUN switch) on the bus: 1 on RP's first
            // tick, k + 1 k ticks later, and back to 0 one tick after RP goes off. It stops
            // at cap + 1 rather than wrapping.
            self.warm.built = true;
            let rp = self.rp;
            self.core(dec_copy(vec![c(rp, CmpOp::Ne, 0), c(w, CmpOp::Le, cap)], w), "control: start-up counter");
            self.core(dec_const(vec![c(rp, CmpOp::Ne, 0), c(w, CmpOp::Gt, cap)], w, cap), "control: start-up counter (stop)");
        }
        if let Some(s) = self.warm.en.get(&n) {
            return Ok(*s);
        }
        let s = self.alloc()?;
        let conds = self.warm_cond(n - 1);
        self.core(dec_const(conds, s, 1), format!("control: start-up delay {n}"));
        self.warm.en.insert(n, s);
        Ok(s)
    }

    /// Conditions that hold from `n` ticks after RP does (n ≥ 0).
    fn warm_cond(&mut self, n: usize) -> Vec<Cond> {
        let rp = c(self.rp, CmpOp::Ne, 0);
        match self.warm.counter {
            _ if n == 0 => vec![rp],
            Some((w, _)) => vec![rp, c(w, CmpOp::Ge, n as i32 + 1)],
            None => vec![c(self.warm.chain[n - 1], CmpOp::Ne, 0)],
        }
    }
}
