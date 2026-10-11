//! `every N` blocks (period ≥ 2, or not pipelined): the block clock and its sample (EI) and
//! commit (ES) pulses, input samples, the block's logic and its state registers.

use ticky_factorio::*;
use ticky_syntax::Diag;

use super::registers::{increments, own_node, Writer};
use super::*;
use crate::fuse::WriterPlan;
use crate::ir::{Lit, V};
use crate::program::{Program, SrcKind};

/// A block that commits every `b.period` ticks; `clock` is its clock signal (period ≥ 2).
pub(super) fn period_block(cg: &mut Cg, p: &Program, bi: usize, b: &crate::program::Block, clock: Option<Sig>, shared: &Shared, live: &[bool]) -> Result<BlockStats, Diag> {
    let first_ent = cg.net.entities.len();
    let (run, rp) = (cg.run, cg.rp);
    let n = b.period as i32;
    let what = format!("block {}", bi + 1);
    let ei = cg.alloc()?;
    let es = cg.alloc()?;
    // Phase (1..=N) at which ES fires; sampling happens at phase 1.
    let phase_es = ((1 + b.depth) % b.period) as i32 + 1;
    // When both pulses share a phase, the very first ES would commit before anything
    // was computed; WARM (set by the first EI) suppresses it.
    let warm = if phase_es == 1 { Some(cg.alloc()?) } else { None };
    let gate = |k: Option<Sig>, phase: i32| -> Vec<Cond> {
        match k {
            Some(k) => vec![c(k, CmpOp::Eq, phase), c(rp, CmpOp::Ne, 0)],
            None => vec![c(rp, CmpOp::Ne, 0)],
        }
    };
    if let Some(k) = clock {
        cg.core(dec_copy(vec![c(k, CmpOp::Lt, n), c(rp, CmpOp::Ne, 0)], k), format!("{what}: clock, period {n}"));
    }
    // Only built when something reads it: a sample, or the warm-up latch.
    let samples = b.srcs.iter().any(|k| !matches!(k, SrcKind::Own(_)));
    if samples || warm.is_some() {
        cg.core(dec_const(gate(clock, 1), ei, 1), format!("{what}: sample pulse"));
    }
    let mut es_conds = gate(clock, phase_es);
    if let Some(w) = warm {
        cg.core(
            dec_const(vec![c(ei, CmpOp::Ne, 0), c(run, CmpOp::Ne, 0), or(c(w, CmpOp::Ne, 0)), c(run, CmpOp::Ne, 0)], w, 1),
            format!("{what}: warm-up latch"),
        );
        es_conds.push(c(w, CmpOp::Ne, 0));
    }
    let es_prefix = es_conds.clone();
    cg.core(dec_const(es_conds, es, 1), format!("{what}: commit pulse"));

    // Sources: own state is read directly; everything else is sampled at EI.
    // Staged inputs share one load (see `ports::staged_inputs`).
    let mut stage = None;
    let mut staged = Vec::new();
    let mut src_ref: Vec<Ref> = Vec::new();
    for &kind in &b.srcs {
        let (raw, name) = shared.raw(p, kind);
        src_ref.push(match kind {
            SrcKind::Own(_) => raw,
            SrcKind::Input(pi) if shared.staged.contains_key(&pi) => {
                stage = Some(shared.staged[&pi]);
                staged.push(raw.sig());
                raw
            }
            _ => cg.sample_ref(raw, ei, &format!("{what}: {name}"))?,
        });
    }
    if let Some(net) = stage {
        cg.staged_samples(net, &staged, ei, &what);
    }
    // Live states' plans, with increments split out (scalar states only).
    let mut plans: Vec<(usize, WriterPlan)> = b.plans.iter().filter(|(si, _)| live[*si]).cloned().collect();
    let incs: Vec<Vec<bool>> = plans
        .iter_mut()
        .map(|(si, plan)| match shared.state(*si) {
            Ref::Op(_) => increments(&b.graph, own_node(&b.graph, &b.srcs, *si), plan),
            Ref::Bun(_) => vec![false; plan.loads.len()],
        })
        .collect();
    let mut roots: Vec<V> = plans.iter().flat_map(|(_, p)| p.operands()).collect();
    roots.extend(b.checks.iter().map(|ck| ck.fail));
    let src = |s: u32| src_ref[s as usize];
    let nodes = cg.logic(&b.graph, &roots, &src, &what)?;
    let loc = |v: V| locate(&b.graph, v, &src, &nodes);
    let lit = |l: &Lit| lit_cond(l, &loc);
    // Checks are read with the commit; the block keeps running.
    let fails = fail_sigs(&b.checks, &loc);
    cg.error_deciders(&es_prefix, &[], &fails, &what);
    for (si, s) in p.states.iter().enumerate() {
        if s.owner != Some(bi) || !live[si] {
            continue;
        }
        let mine: Vec<usize> = (0..plans.len()).filter(|&i| plans[i].0 == si).collect();
        let ws: Vec<Writer> =
            mine.iter().map(|&i| Writer { en: es, prefix: es_prefix.clone(), plan: &plans[i].1, val: &loc, lit: &lit, lit_eg: &lit }).collect();
        let my_incs: Vec<Vec<bool>> = mine.iter().map(|&i| incs[i].clone()).collect();
        let name = format!("state {}", s.display_name());
        match shared.state(si) {
            Ref::Bun(x) => cg.bregister(x, &s.binit, &ws, &name)?,
            r => cg.register_incs(r.sig(), s.init, &ws, &my_incs, &name)?,
        }
    }
    cg.flush_shared(false);
    Ok(BlockStats {
        span: b.span,
        requested: b.requested,
        period: b.period,
        depth: b.depth,
        combinators: cg.combinators_since(first_ent),
        latency: None,
    })
}
