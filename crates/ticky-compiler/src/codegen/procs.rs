//! Sequential processes (`main` and named processes): the step machine — step timer, program
//! counter, per-step commit deciders, return-address registers — and their variables.

use std::collections::HashMap;

use ticky_factorio::*;
use ticky_syntax::Diag;

use super::registers::Writer;
use super::*;
use crate::fuse::{LoadVal, WriterPlan};
use crate::ir::{Lit, V};
use crate::program::{Next, Program, SrcKind, StepKind, WaitN};

pub(super) fn main_proc(
    cg: &mut Cg,
    p: &Program,
    m: &crate::program::MainProc,
    shared: &Shared,
    any: Sig,
    live: &[bool],
) -> Result<MainStats, Diag> {
    let first_ent = cg.net.entities.len();
    let (run, rp, st) = (cg.run, cg.rp, cg.st);
    let g = &m.graph;
    let pc = cg.alloc()?;
    let tm = cg.alloc()?;
    let pc_of = |s: Option<usize>| s.map_or(0, |i| i as i32 + 1);

    // Step timer: ticks since the current step started.
    cg.counter(tm, vec![c(any, CmpOp::Eq, 0), c(rp, CmpOp::Ne, 0)], &format!("{}: step timer", m.name));

    // Sources: own variables directly, inputs and other processes' state sampled at each
    // step start, and live (unsampled) versions for `wait until`.
    let mut src_ref: Vec<Ref> = Vec::new();
    for &kind in &m.srcs {
        let (raw, name) = shared.raw(p, kind);
        src_ref.push(match kind {
            SrcKind::Input(_) | SrcKind::Foreign(_) | SrcKind::Ticks => cg.sample_ref(raw, any, &format!("{}: {name}", m.name))?,
            _ => raw,
        });
    }
    let src = |s: u32| src_ref[s as usize];
    let mut steps = m.steps.clone();
    for s in &mut steps {
        s.plans.retain(|(si, _)| live[*si]);
    }
    let roots: Vec<V> = steps.iter().flat_map(|s| s.roots()).collect();
    let nodes = cg.logic(g, &roots, &src, &m.name)?;
    let loc = |v: V| locate(g, v, &src, &nodes);
    let opnd = |v: V| loc(v).op();
    let sig_of = |v: V| loc(v).sig();
    let lit = |l: &Lit| lit_cond(l, &loc);
    // A condition as decider terms: its condition lists if fused, else `node != 0` / `== 0`.
    let cond_terms = |plan: &crate::fuse::CondPlan, neg: bool| -> CDnf {
        match (if neg { &plan.neg } else { &plan.pos }, &plan.pos, &plan.neg) {
            (Some(d), Some(_), Some(_)) => lits(d, &lit),
            (Some(d), _, _) if !neg => lits(d, &lit),
            _ => vec![vec![c(sig_of(plan.node), if neg { CmpOp::Eq } else { CmpOp::Ne }, 0)]],
        }
    };

    // The program counter holds while RUN is on and moves by adding offsets: the commit
    // decider adds the offset to `fall[i]` (the jump, call, halt or the branch's `else`
    // target) when it pulses ANY; a branch taken adds the difference one tick later (when its
    // condition is read, as before); a return drops to 0 and then adds the return address.
    let fall: Vec<Option<i32>> = steps
        .iter()
        .map(|s| match &s.kind {
            StepKind::Run(Next::Goto(t)) | StepKind::WaitUntil(_, t) | StepKind::WaitTicks(_, t) => Some(pc_of(*t)),
            StepKind::Run(Next::Branch(_, _, b)) => Some(pc_of(*b)),
            StepKind::Run(Next::Call { entry, .. }) => Some(pc_of(Some(*entry))),
            StepKind::Run(Next::Return { .. }) => Some(0),
        })
        .collect();

    // Commit deciders.
    let mut cm: Vec<Option<(Sig, Vec<Cond>)>> = Vec::new();
    let mut stats = Vec::new();
    for (i, s) in steps.iter().enumerate() {
        let line = format!("{} step {}", m.name, i + 1);
        let here = i as i32 + 1;
        let mut prefix = vec![c(pc, CmpOp::Eq, here), c(any, CmpOp::Eq, 0)];
        let mut extra: CDnf = vec![vec![]];
        // Commits land `depth` ticks after the step starts (at least one), when everything
        // they load is ready: the decider fires one tick before.
        let settle = s.depth.max(1) as i32 - 1;
        let ready = s.wait_ready as i32;
        let duration = match &s.kind {
            StepKind::Run(_) => {
                prefix.push(c(tm, CmpOp::Eq, settle));
                format!("{} ticks", settle + 2)
            }
            StepKind::WaitUntil(plan, _) => {
                let terms = cond_terms(plan, false);
                if terms.is_empty() || g.as_const(plan.node) == Some(0) {
                    cm.push(None);
                    stats.push(StepStats { span: s.span, duration: "waits forever".into(), self_loop: false });
                    continue;
                }
                if ready > 0 {
                    prefix.push(c(tm, CmpOp::Ge, ready));
                }
                extra = terms;
                format!("waits (≥ {} ticks)", ready + 2)
            }
            StepKind::WaitTicks(WaitN::Const(n), _) => {
                prefix.push(c(tm, CmpOp::Eq, (n - 2).max(0)));
                format!("{} ticks", n.max(&2))
            }
            StepKind::WaitTicks(WaitN::Dyn(mv), _) => {
                prefix.push(Cond { second: opnd(*mv), ..c(tm, CmpOp::Ge, 0) });
                if ready > 0 {
                    prefix.push(c(tm, CmpOp::Ge, ready));
                }
                format!("n ticks (≥ {})", ready + 2)
            }
        };
        // Checks: the step only commits if they all pass; otherwise an error decider records
        // the first failure's code and pulses ANY without a commit, so the PC drops to 0
        // (halted).
        let fails = fail_sigs(&s.checks, &loc);
        let base = prefix.clone();
        for (f, _) in &fails {
            prefix.push(cg.passes(*f));
        }
        // A failure halts: the PC drops to 0.
        cg.error_deciders(&base, &[(any, 1), (pc, -here)], &fails, &line);
        let cms = cg.alloc()?;
        let mut outs = vec![out_const(cms, 1), out_const(any, 1)];
        if let Some(t) = fall[i] {
            outs.push(out_const(pc, t - here));
        }
        cg.core(dec(distribute(&prefix, &extra), outs), format!("{line}: commit"));
        cm.push(Some((cms, prefix)));
        let self_loop = s.targets().contains(&Some(i));
        stats.push(StepStats { span: s.span, duration, self_loop });
    }

    // Return-address registers, one per subroutine.
    let mut ret_sig: HashMap<String, Sig> = HashMap::new();
    for s in &steps {
        if let StepKind::Run(Next::Call { func, .. }) = &s.kind {
            if !ret_sig.contains_key(func) {
                let r = cg.alloc()?;
                ret_sig.insert(func.clone(), r);
            }
        }
    }

    // Program counter.
    let mut pc_loads: Vec<Kind> = Vec::new();
    for (i, s) in steps.iter().enumerate() {
        let Some((cms, _)) = &cm[i] else { continue };
        let on = [c(*cms, CmpOp::Ne, 0)];
        match &s.kind {
            StepKind::Run(Next::Goto(_)) | StepKind::WaitUntil(..) | StepKind::WaitTicks(..) | StepKind::Run(Next::Call { .. }) => {}
            StepKind::Run(Next::Branch(plan, a, b)) => {
                let terms = cond_terms(plan, false);
                if a != b && !terms.is_empty() {
                    pc_loads.push(dec_const(distribute(&on, &terms), pc, pc_of(*a) - pc_of(*b)));
                }
            }
            // Jump to the step the return-address register holds (if never called, never reached).
            StepKind::Run(Next::Return { func }) => {
                if let Some(&r) = ret_sig.get(func) {
                    pc_loads.push(arith(Operand::Sig(r), ArOp::Mul, Operand::Sig(*cms), pc));
                }
            }
        }
    }
    cg.core(dec_copy(vec![c(run, CmpOp::Ne, 0)], pc), format!("{}: program counter (hold)", m.name));
    cg.core(dec_const(vec![c(st, CmpOp::Ne, 0)], pc, pc_of(Some(m.entry))), format!("{}: program counter (start)", m.name));
    for k in pc_loads {
        cg.core(k, format!("{}: program counter (next step)", m.name));
    }

    // Variables.
    for (si, s) in p.states.iter().enumerate() {
        if s.owner != Some(m.owner) || !live[si] {
            continue;
        }
        let mut ws = Vec::new();
        for (i, step) in steps.iter().enumerate() {
            let Some((cms, prefix)) = &cm[i] else { continue };
            for (w, plan) in &step.plans {
                if *w == si {
                    ws.push(Writer { en: *cms, prefix: prefix.clone(), plan, val: &loc, lit: &lit, lit_eg: &lit });
                }
            }
        }
        let name = format!("variable {}", s.display_name());
        match shared.state(si) {
            Ref::Bun(x) => cg.bregister(x, &s.binit, &ws, &name)?,
            r => cg.register(r.sig(), s.init, &ws, &name)?,
        }
    }
    for (func, &r) in &ret_sig {
        let plans: Vec<(Sig, Vec<Cond>, WriterPlan)> = steps
            .iter()
            .enumerate()
            .filter_map(|(i, s)| match (&s.kind, &cm[i]) {
                (StepKind::Run(Next::Call { func: f, cont, .. }), Some((cms, prefix))) if f == func => {
                    let load = crate::fuse::Load { guard: vec![vec![]], val: LoadVal::Const(pc_of(*cont)), direct: false };
                    Some((*cms, prefix.clone(), WriterPlan { loads: vec![load], keep: None }))
                }
                _ => None,
            })
            .collect();
        let ws: Vec<Writer> =
            plans.iter().map(|(en, prefix, plan)| Writer { en: *en, prefix: prefix.clone(), plan, val: &loc, lit: &lit, lit_eg: &lit }).collect();
        cg.register(r, 0, &ws, &format!("{}: return address of `{func}`", m.name))?;
    }
    Ok(MainStats { name: m.name.clone(), steps: stats, combinators: cg.combinators_since(first_ent) })
}
