//! Blocks that run every tick: a balanced pipeline reading inputs directly, with operands
//! delayed to their consumer's iteration (`at_ref`), registers enabled by the start-up delay
//! line, and combinational outputs read straight off the pipeline.

use std::collections::HashMap;

use ticky_factorio::*;
use ticky_syntax::Diag;

use super::registers::{accumulator, Writer};
use super::*;
use crate::fuse::{is_true, LoadVal, WriterPlan};
use crate::ir::{Lit, Op, V};
use crate::program::Program;

/// A block that runs every tick: logic is a balanced pipeline reading inputs directly.
/// Returns where each combinational output (`comb`) of the block can be read.
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
) -> Result<(HashMap<usize, Ref>, u32), Diag> {
    let what = format!("block {}", bi + 1);
    let g = &b.graph;
    let tau = |v: V| pipe.tau[v as usize];
    let owned: Vec<usize> = (0..p.states.len()).filter(|&si| p.states[si].owner == Some(bi) && live[si]).collect();
    let registers = owned.iter().any(|si| !comb.contains(si));
    // Commit only once the pipeline holds values computed from inputs read after the start.
    let (en, en_prefix) = if registers {
        let en = cg.warm(pipe.latency as usize + 1)?;
        (en, if pipe.latency == 0 { cg.rp } else { cg.warm(pipe.latency as usize)? })
    } else {
        (cg.rp, cg.rp)
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
    let mut node_ref: HashMap<V, Ref> = HashMap::new();
    for &v in &nodes {
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
    let mut delayed: HashMap<(V, i32), Ref> = HashMap::new();
    // The value of `u` for the current iteration, on the wire at offset `at`.
    let mut at_ref = |cg: &mut Cg, u: V, at: i32| -> Result<Ref, Diag> {
        let base = match *g.op(u) {
            Op::Const(k) => return Ok(Ref::Op(Operand::Const(k))),
            Op::BConst(_) => return Ok(node_ref[&u]), // constant: no timing
            Op::Src(s) => src_ref[s as usize],
            _ => node_ref[&u],
        };
        let t = tau(u).expect("timed node");
        assert!(t <= at, "pipeline schedule: value needed before it exists");
        let mut cur = base;
        for d in 1..=(at - t) {
            cur = match delayed.get(&(u, t + d)) {
                Some(r) => *r,
                None => {
                    let r = match cur {
                        Ref::Bun(prev) => {
                            let next = cg.bnew();
                            let each = cg.each;
                            let id = cg.loose(arith(Operand::Sig(each), ArOp::Add, Operand::Const(0), each), format!("{what}: delay"));
                            cg.bread(prev, id, false);
                            cg.bprod(next, id);
                            Ref::Bun(next)
                        }
                        r => {
                            let s = cg.alloc()?;
                            cg.core(arith(r.op(), ArOp::Add, Operand::Const(0), s), format!("{what}: delay"));
                            Ref::Op(Operand::Sig(s))
                        }
                    };
                    delayed.insert((u, t + d), r);
                    r
                }
            };
        }
        Ok(cur)
    };
    let as_sig = |o: Operand| match o {
        Operand::Sig(s) => s,
        Operand::Const(_) => unreachable!("constant where a signal is required"),
    };
    for &v in &nodes {
        let Some(&out_ref) = node_ref.get(&v) else { continue };
        if matches!(g.op(v), Op::BConst(_)) {
            cg.emit_bundle(g, v, out_ref.bun(), &|_| unreachable!(), &|_| None, &|_| false, &what);
            continue;
        }
        let t = tau(v).unwrap() - 1;
        if let Op::Bun(_) | Op::BMux { .. } | Op::BDec(_) | Op::BSelect(..) | Op::BSelectAt(..) | Op::BSel(..) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_) | Op::AGet(..) | Op::BDot(..) = g.op(v) {
            // Operands as of this node's input tick, then the combinators.
            let mut ops: HashMap<V, Ref> = HashMap::new();
            for u in g.operands(v) {
                let r = at_ref(cg, u, t)?;
                ops.insert(u, r);
            }
            let look = |u: V| ops[&u];
            match out_ref {
                Ref::Bun(o) => cg.emit_bundle(g, v, o, &look, &|_| None, &|_| false, &what),
                r => cg.emit_from_bundle(g, v, r.sig(), 1, None, &look, &what),
            }
            continue;
        }
        let out = out_ref.sig();
        match g.op(v).clone() {
            Op::Ar(op, a, bb) => {
                let (x, y) = (at_ref(cg, a, t)?.op(), at_ref(cg, bb, t)?.op());
                cg.core(arith(x, op, y, out), format!("{what}: arithmetic"));
            }
            Op::Cmp(op, a, bb) => {
                let (x, y) = (as_sig(at_ref(cg, a, t)?.op()), at_ref(cg, bb, t)?.op());
                cg.core(dec_const(vec![Cond { second: y, ..c(x, op, 0) }], out, 1), format!("{what}: comparison"));
            }
            Op::Mux { .. } | Op::Sel(_) => {
                let arms: Vec<(V, V)> = match g.op(v) {
                    Op::Mux { t, f, a, b } => vec![(*t, *a), (*f, *b)],
                    Op::Sel(arms) => arms.clone(),
                    _ => unreachable!(),
                };
                for (cond, val) in arms {
                    // An arm worth 0 adds nothing (and its condition isn't computed).
                    if g.as_const(val) == Some(0) {
                        continue;
                    }
                    let cs = as_sig(at_ref(cg, cond, t)?.op());
                    match at_ref(cg, val, t)?.op() {
                        Operand::Const(0) => {}
                        Operand::Const(k) => {
                            cg.core(dec_const(vec![c(cs, CmpOp::Ne, 0)], out, k), format!("{what}: select"));
                        }
                        Operand::Sig(s) => {
                            cg.core(arith(Operand::Sig(s), ArOp::Mul, Operand::Sig(cs), out), format!("{what}: select"));
                        }
                    }
                }
            }
            Op::Dec(arms) => {
                for (d, k) in arms {
                    let mut terms: CDnf = Vec::new();
                    for term in &d {
                        let mut conds = Vec::new();
                        for l in term {
                            let (x, y) = (as_sig(at_ref(cg, l.a, t)?.op()), at_ref(cg, l.b, t)?.op());
                            conds.push(Cond { second: y, ..c(x, l.op, 0) });
                        }
                        terms.push(conds);
                    }
                    cg.core(dec_const(distribute(&[], &terms), out, k), format!("{what}: condition"));
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
                ready.insert((v, guard_at), Ref::Op(at_ref(cg, v, guard_at)?.op()));
            }
            if let LoadVal::Node(v) = l.val {
                ready.insert((v, 0), at_ref(cg, v, 0)?);
            }
        }
        if let Some(k) = &plan.keep {
            for v in crate::ir::dnf_operands(k) {
                ready.insert((v, 0), Ref::Op(at_ref(cg, v, 0)?.op()));
            }
        }
    }
    let mut acc_w: Vec<(usize, Operand)> = Vec::new();
    for (si, a) in &accs {
        acc_w.push((*si, at_ref(cg, a.w, -1)?.op()));
        for v in acc_conds(a) {
            ready.insert((v, 0), Ref::Op(at_ref(cg, v, 0)?.op()));
        }
    }
    // Combinational outputs: the value at offset 0, or one tick later when other states of
    // the block go through registers (whose outputs show values a tick later), so that all
    // outputs of an iteration change together.
    // Conditions checked on the commit tick (direct loads) also push outputs a tick later.
    let late = registers || plans.iter().any(|(si, p)| comb.contains(si) && p.loads.iter().any(|l| l.direct));
    let o = if late { 1 } else { 0 };
    let mut direct: HashMap<usize, Ref> = HashMap::new();
    for (si, plan) in &plans {
        if !comb.contains(si) {
            continue;
        }
        let r = match (plan.loads.as_slice(), plan.loads.first().map(|l| is_true(&l.guard))) {
            ([l], Some(true)) => match l.val {
                LoadVal::Const(k) => Ref::Op(Operand::Const(k)),
                LoadVal::Node(v) => at_ref(cg, v, o)?,
            },
            _ => {
                // Constants under (mutually exclusive) conditions: one decider each.
                let out = cg.alloc()?;
                for l in &plan.loads {
                    let LoadVal::Const(k) = l.val else { unreachable!("checked by combinational()") };
                    if k == 0 {
                        continue;
                    }
                    let mut terms: CDnf = Vec::new();
                    for term in &l.guard {
                        let mut conds = Vec::new();
                        for lit in term {
                            let (x, y) = (at_ref(cg, lit.a, o - 1)?.sig(), at_ref(cg, lit.b, o - 1)?.op());
                            conds.push(Cond { second: y, ..c(x, lit.op, 0) });
                        }
                        terms.push(conds);
                    }
                    cg.core(dec_const(distribute(&[], &terms), out, k), format!("{what}: {}", p.states[*si].display_name()));
                }
                Ref::Op(Operand::Sig(out))
            }
        };
        direct.insert(*si, r);
    }
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
            .map(|(_, plan)| Writer { en, prefix: vec![c(en_prefix, CmpOp::Ne, 0)], plan, val: &val, lit: &lit, lit_eg: &lit_eg })
            .collect();
        match shared.state(si) {
            Ref::Bun(x) => cg.bregister(x, &s.binit, &ws, &name)?,
            r => cg.register(r.sig(), s.init, &ws, &name)?,
        }
    }
    Ok((direct, if registers { 1 } else { o as u32 }))
}
