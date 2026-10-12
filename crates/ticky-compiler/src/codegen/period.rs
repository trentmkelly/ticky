//! `every N` blocks (period ≥ 2, or not pipelined): the block clock and its sample (EI) and
//! commit (ES) pulses, input samples, the block's logic and its state registers.

use ticky_factorio::*;
use ticky_syntax::Diag;

use super::registers::{increments, own_node, StageIn, Writer};
use super::*;
use crate::fuse::WriterPlan;
use crate::ir::{Lit, V};
use crate::program::{Program, SrcKind};

/// A block clock: `sig` counts 1..=N (from the RUN switch's +1, copied while below N). All
/// clocks start together, so blocks of the same period share one; `build` is set for the
/// block that builds it. (A block whose period divides another's could test two phases of
/// the longer clock, but the commit pulse's conditions must stay one AND-term: register
/// enable pulses and checks extend them.)
#[derive(Copy, Clone)]
pub(super) struct Clock {
    pub(super) sig: Sig,
    pub(super) build: bool,
    sample: Pulse,
    commit: Pulse,
    warm: Option<Sig>,
}

#[derive(Copy, Clone)]
struct Pulse {
    sig: Sig,
    build: bool,
}

/// The clock of each block (period ≥ 2 and not pipelined).
pub(super) fn clocks(cg: &mut Cg, p: &Program) -> Result<Vec<Option<Clock>>, Diag> {
    let mut out: Vec<Option<Clock>> = Vec::new();
    let mut built: Vec<(u32, Sig)> = Vec::new();
    let mut samples: Vec<(u32, Sig)> = Vec::new();
    let mut commits: Vec<(u32, u32, Sig, Option<Sig>)> = Vec::new();
    for b in &p.blocks {
        if b.period < 2 || b.pipe.is_some() {
            out.push(None);
            continue;
        }
        let (sig, build) = match built.iter().find(|(n, _)| *n == b.period) {
            Some(&(_, sig)) => (sig, false),
            None => {
                let sig = cg.alloc()?;
                built.push((b.period, sig));
                (sig, true)
            }
        };
        let phase = (1 + b.depth) % b.period + 1;
        let needs_sample = phase == 1 || b.srcs.iter().any(|k| !matches!(k, SrcKind::Own(_)));
        let sample = match samples.iter().find(|(n, _)| *n == b.period) {
            Some(&(_, sig)) => Pulse { sig, build: false },
            None => {
                let sig = cg.alloc()?;
                if needs_sample {
                    samples.push((b.period, sig));
                }
                Pulse {
                    sig,
                    build: needs_sample,
                }
            }
        };
        // Equal periods and commit phases have exactly the same enable history,
        // including the first-iteration suppression when the commit wraps to phase 1.
        let (commit, warm) = match commits
            .iter()
            .find(|(n, ph, _, _)| *n == b.period && *ph == phase)
        {
            Some(&(_, _, sig, warm)) => (Pulse { sig, build: false }, warm),
            None => {
                let sig = cg.alloc()?;
                let warm = if phase == 1 { Some(cg.alloc()?) } else { None };
                commits.push((b.period, phase, sig, warm));
                (Pulse { sig, build: true }, warm)
            }
        };
        let clock = Clock {
            sig,
            build,
            sample,
            commit,
            warm,
        };
        out.push(Some(clock));
    }
    Ok(out)
}

/// A block that commits every `b.period` ticks; `clock` is its clock (period ≥ 2).
pub(super) fn period_block(cg: &mut Cg, p: &Program, bi: usize, b: &crate::program::Block, clock: Option<Clock>, shared: &Shared, live: &[bool]) -> Result<BlockStats, Diag> {
    let first_ent = cg.net.entities.len();
    let (run, rp) = (cg.run, cg.rp);
    let n = b.period as i32;
    let what = format!("block {}", bi + 1);
    let ei = match clock {
        Some(k) => k.sample.sig,
        None => cg.alloc()?,
    };
    let es = match clock {
        Some(k) => k.commit.sig,
        None => cg.alloc()?,
    };
    // Phase (1..=N) at which ES fires; sampling happens at phase 1.
    let phase_es = ((1 + b.depth) % b.period) as i32 + 1;
    // When both pulses share a phase, the very first ES would commit before anything
    // was computed; WARM (set by the first EI) suppresses it.
    let warm = match clock {
        Some(k) => k.warm,
        None if phase_es == 1 => Some(cg.alloc()?),
        None => None,
    };
    let gate = |k: Option<Clock>, phase: i32| -> Vec<Cond> {
        match k {
            Some(k) => vec![c(k.sig, CmpOp::Eq, phase), c(rp, CmpOp::Ne, 0)],
            None => vec![c(rp, CmpOp::Ne, 0)],
        }
    };
    if let Some(k) = clock.filter(|k| k.build) {
        cg.core(
            dec_copy(vec![c(k.sig, CmpOp::Lt, n), c(rp, CmpOp::Ne, 0)], k.sig),
            format!("{what}: clock, period {n}"),
        );
    }
    // Only built when something reads it: a sample, or the warm-up latch.
    let samples = b.srcs.iter().any(|k| !matches!(k, SrcKind::Own(_)));
    if clock.map_or(samples || warm.is_some(), |k| k.sample.build) {
        cg.core(
            dec_const(gate(clock, 1), ei, 1),
            format!("{what}: sample pulse"),
        );
    }
    let mut es_conds = gate(clock, phase_es);
    if let Some(w) = warm {
        if clock.map_or(true, |k| k.commit.build) {
            cg.core(
                dec_const(
                    vec![
                        c(ei, CmpOp::Ne, 0),
                        c(run, CmpOp::Ne, 0),
                        or(c(w, CmpOp::Ne, 0)),
                        c(run, CmpOp::Ne, 0),
                    ],
                    w,
                    1,
                ),
                format!("{what}: warm-up latch"),
            );
        }
        es_conds.push(c(w, CmpOp::Ne, 0));
    }
    let es_prefix = es_conds.clone();
    if clock.map_or(true, |k| k.commit.build) {
        cg.core(dec_const(es_conds, es, 1), format!("{what}: commit pulse"));
    }

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
    let roots = |plans: &[(usize, WriterPlan)]| -> Vec<V> {
        let mut r: Vec<V> = plans.iter().flat_map(|(_, p)| p.operands()).collect();
        r.extend(b.checks.iter().map(|ck| ck.fail));
        r
    };
    // Staged loads (see `registers::Cg::stage_loads`).
    let before = roots(&plans);
    let ins: Vec<StageIn> = plans
        .iter_mut()
        .zip(&incs)
        .enumerate()
        .filter_map(|(i, ((si, plan), inc))| match shared.state(*si) {
            r @ Ref::Op(_) => Some(StageIn { key: i, writer: 0, x: r.sig(), plan, incs: inc }),
            Ref::Bun(_) => None,
        })
        .collect();
    let mut staging = cg.stage_loads(&b.graph, &before, ins);
    let mut vals = staging.vals();
    let src = |s: u32| src_ref[s as usize];
    let nodes = cg.logic(&b.graph, &roots(&plans), &src, &mut vals, &what)?;
    staging.settle(&vals);
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
            mine.iter().map(|&i| Writer { en: es, prefix: es_prefix.clone(), plan: &plans[i].1, val: &loc, lit: &lit, lit_eg: &lit, stage: staging.of(i, plans[i].1.loads.len()) }).collect();
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
