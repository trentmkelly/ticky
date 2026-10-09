//! One-tick pipelining for `every tick:` blocks.
//!
//! A block can run every tick when no state feeds back into itself through a combinator:
//! each state's next value must be ready on the same tick its old value is (it is the old
//! value, a constant, or depends on own state only through conditions that the load
//! deciders check themselves). Everything computed from inputs then flows through the
//! combinators continuously, `latency` ticks behind, with short delay chains so that every
//! combinator sees operands from the same iteration.
//!
//! Accumulators (`x += w`, optionally under a condition, where `w` doesn't depend on the
//! block's own state) also run every tick: `w` is summed straight into the register's
//! feedback wire.
//!
//! Time offsets (τ) are relative to the iteration a value belongs to: own state is at 0
//! (the register output during that iteration's tick), inputs are read at -latency.

use ticky_factorio::ArOp;

use crate::fuse::{is_true, LoadVal, WriterPlan};
use crate::ir::{dnf_operands, Dnf, Graph, Iv, Op, V};
use crate::program::SrcKind;

pub struct Pipe {
    /// Ticks between reading the inputs and the iteration that uses them.
    pub latency: u32,
    /// Time offset of each node (by node index); `None` for constants and unused nodes.
    pub tau: Vec<Option<i32>>,
    /// Registers updated as accumulators.
    pub accs: Vec<(usize, Acc)>,
}

/// Depth through own-state paths only; `None` for values that don't depend on own state.
fn own_depths(g: &Graph, srcs: &[SrcKind]) -> Vec<Option<i32>> {
    let mut d: Vec<Option<i32>> = vec![None; g.nodes.len()];
    for v in 0..g.nodes.len() as V {
        d[v as usize] = match *g.op(v) {
            Op::Src(s) => matches!(srcs[s as usize], SrcKind::Own(_)).then_some(0),
            Op::Const(_) => None,
            _ => g.operands(v).iter().filter_map(|o| d[*o as usize]).max().map(|m| m + 1),
        };
    }
    d
}

/// Depth from the block's inputs (for values that don't depend on own state).
fn input_depths(g: &Graph) -> Vec<i32> {
    let mut d = vec![0i32; g.nodes.len()];
    for v in 0..g.nodes.len() as V {
        let ops = g.operands(v);
        if !ops.is_empty() {
            d[v as usize] = 1 + ops.iter().map(|o| d[*o as usize]).max().unwrap();
        }
    }
    d
}

/// A register updated every tick as `x += w`, except when one of `consts` applies.
#[derive(Clone, Debug)]
pub struct Acc {
    /// The increment (already zero whenever the plan says "keep").
    pub w: V,
    /// Constant loads that override the increment: `(condition, value)`.
    pub consts: Vec<(Dnf, i32)>,
    /// When none of `consts` applies (the accumulator adds `w`).
    pub otherwise: Dnf,
}

/// The accumulator form of a plan, if it is one: `x = x + w` (or `x - w`), possibly under a
/// condition and alongside constant loads (e.g. a reset), with `w` and that condition
/// independent of the block's own state.
fn accumulator(g: &mut Graph, plan: &WriterPlan, own: V, od: &[Option<i32>]) -> Option<Acc> {
    let free = |x: V| od[x as usize].is_none();
    let mut add: Option<(Dnf, V)> = None;
    let mut consts = Vec::new();
    for l in &plan.loads {
        match l.val {
            LoadVal::Const(k) => consts.push((l.guard.clone(), k)),
            LoadVal::Node(v) if add.is_none() => {
                let w = match *g.op(v) {
                    Op::Ar(ArOp::Add, a, b) if a == own && free(b) => b,
                    Op::Ar(ArOp::Add, a, b) if b == own && free(a) => a,
                    Op::Ar(ArOp::Sub, a, b) if a == own && free(b) => {
                        let z = g.konst(0);
                        g.ar(ArOp::Sub, z, b)
                    }
                    _ => return None,
                };
                add = Some((l.guard.clone(), w));
            }
            LoadVal::Node(_) => return None,
        }
    }
    let (guard, w) = add?;
    let mut otherwise: Dnf = vec![vec![]];
    for (d, _) in &consts {
        otherwise = crate::fuse::and_dnf(&otherwise, &crate::fuse::negate(d)?)?;
    }
    let w = if is_true(&guard) {
        w
    } else {
        if !dnf_operands(&guard).all(free) {
            return None;
        }
        // Add nothing when the condition is false.
        let c = g.dec(vec![(guard, 1)], Iv::BOOL);
        let z = g.konst(0);
        g.mux(c, w, z)
    };
    Some(Acc { w, consts, otherwise })
}

/// Plans one-tick pipelining for a block, or `None` if a state feeds back through logic.
/// On success, accumulator registers are removed from `plans` (they're in `Pipe::accs`).
pub fn plan(g: &mut Graph, srcs: &[SrcKind], plans: &mut Vec<(usize, WriterPlan)>) -> Option<Pipe> {
    let od = own_depths(g, srcs);
    let own_node = |g: &mut Graph, si: usize| {
        srcs.iter().position(|k| *k == SrcKind::Own(si)).map(|id| g.src(id as u32))
    };

    // Accumulators first; everything else must be ready at offset 0.
    let mut accs = Vec::new();
    let mut rest = Vec::new();
    for (si, p) in plans.iter() {
        if let Some(own) = own_node(g, *si) {
            if let Some(w) = accumulator(g, p, own, &od) {
                accs.push((*si, w));
                continue;
            }
        }
        rest.push((*si, p.clone()));
    }
    let od = own_depths(g, srcs); // accumulator() may have added nodes
    for (_, a) in &accs {
        // Constant loads are checked on the commit tick, like direct loads.
        let conds = a.consts.iter().flat_map(|(d, _)| dnf_operands(d)).chain(dnf_operands(&a.otherwise));
        if !conds.into_iter().all(|v| od[v as usize].is_none_or(|d| d <= 0)) {
            return None;
        }
    }
    let at_most = |nodes: &mut dyn Iterator<Item = V>, limit: i32| {
        let mut ok = true;
        for v in nodes {
            ok &= od[v as usize].is_none_or(|d| d <= limit);
        }
        ok
    };
    for (_, p) in &rest {
        for l in &p.loads {
            let ok = match (&l.val, l.direct, is_true(&l.guard)) {
                (_, true, _) => at_most(&mut dnf_operands(&l.guard), 0),
                (LoadVal::Node(v), _, true) => at_most(&mut [*v].into_iter(), 0),
                (LoadVal::Const(_), _, true) => true,
                (LoadVal::Node(v), false, false) => {
                    at_most(&mut [*v].into_iter(), 0) && at_most(&mut dnf_operands(&l.guard), -1)
                }
                (LoadVal::Const(_), false, false) => at_most(&mut dnf_operands(&l.guard), -1),
            };
            if !ok {
                return None;
            }
        }
        if let Some(k) = &p.keep {
            if !at_most(&mut dnf_operands(k), 0) {
                return None;
            }
        }
    }

    // Each use of an input-derived value fixes a lower bound on the input latency.
    let din = input_depths(g);
    let mut need: Vec<(V, i32)> = Vec::new(); // (value, offset it's needed at)
    for (_, p) in &rest {
        for l in &p.loads {
            let guard_at = if l.direct || is_true(&l.guard) { 0 } else { -1 };
            need.extend(dnf_operands(&l.guard).map(|v| (v, guard_at)));
            if let LoadVal::Node(v) = l.val {
                need.push((v, 0));
            }
        }
        if let Some(k) = &p.keep {
            need.extend(dnf_operands(k).map(|v| (v, 0)));
        }
    }
    for (_, a) in &accs {
        need.push((a.w, -1));
        need.extend(a.consts.iter().flat_map(|(d, _)| dnf_operands(d)).map(|v| (v, 0)));
        need.extend(dnf_operands(&a.otherwise).map(|v| (v, 0)));
    }
    let roots: Vec<V> = need.iter().map(|(v, _)| *v).collect();
    let live = g.reachable(&roots);
    let mut latency = 0i32;
    let free = |v: V| od[v as usize].is_none() && g.as_const(v).is_none();
    for &(v, at) in &need {
        if free(v) {
            latency = latency.max(din[v as usize] - at);
        }
    }
    for &v in &live {
        if let Some(t) = od[v as usize] {
            for u in g.operands(v) {
                if free(u) {
                    latency = latency.max(din[u as usize] - (t - 1));
                }
            }
        }
    }

    let mut tau: Vec<Option<i32>> = vec![None; g.nodes.len()];
    for v in live {
        tau[v as usize] = match *g.op(v) {
            Op::Const(_) => None,
            Op::Src(s) if matches!(srcs[s as usize], SrcKind::Own(_)) => Some(0),
            Op::Src(_) => Some(-latency),
            _ => g.operands(v).iter().filter_map(|o| tau[*o as usize]).max().map(|m| m + 1),
        };
    }
    *plans = rest;
    Some(Pipe { latency: latency as u32, tau, accs })
}
