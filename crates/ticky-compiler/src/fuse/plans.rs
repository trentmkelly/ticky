//! Register updates as guarded loads: [`Fuser::plan`] splits `next` along its selects
//! ([`Fuser::split`]) into loads; [`Fuser::writer_plan`] marks constant loads that check
//! their own guard (`direct`) and the hold condition (`keep`).

use super::*;
use crate::ir::{Dnf, V};

impl Fuser<'_> {
    /// Guarded loads that set a register to `next`; `own` is the register's own value (for
    /// paths that keep it). `None` if the register never changes.
    pub fn plan(&mut self, next: V, own: Option<V>) -> Option<Vec<Load>> {
        if Some(next) == own {
            return None;
        }
        let mut loads = Vec::new();
        self.split(next, vec![vec![]], own, &mut loads);
        Some(loads)
    }

    pub(super) fn split(&mut self, v: V, guard: Dnf, own: Option<V>, loads: &mut Vec<Load>) {
        if Some(v) == own {
            return; // this path keeps the current value
        }
        if guard.is_empty() {
            return; // unreachable path
        }
        // Splitting a select only pays when a path keeps the old value or loads a constant
        // (otherwise it just multiplies loads), and the number of loads stays small.
        let worth = |this: &Self, x: V| Some(x) == own || this.g.as_const(x).is_some() || this.mentions(x, own);
        // A running maximum is cheaper as one selector than as loads per candidate.
        if self.argmax_chain(v).is_some() {
            let r = self.rebuild(v);
            loads.push(Load { guard, val: LoadVal::Node(r), direct: false });
            return;
        }
        if let Some((t, f, a, b)) = self.g.as_mux(v) {
            // The top-level split is cheap (two loads) and saves the select stage.
            let top = is_true(&guard);
            let useful = (top || worth(self, a) || worth(self, b)) && loads.len() < MAX_LOADS;
            if let (true, Some(dt), Some(df)) = (useful, self.dnf(t, false), self.dnf(f, false)) {
                if let (Some(gt), Some(gf)) = (and(&guard, &dt), and(&guard, &df)) {
                    self.split(a, gt, own, loads);
                    self.split(b, gf, own, loads);
                    return;
                }
            }
        }
        let val = match self.g.as_const(v) {
            Some(k) => LoadVal::Const(k),
            None => {
                // A bool-valued node can itself split into constant loads: 1 when it holds,
                // 0 (stop holding) otherwise.
                if self.g.is_bool(v) {
                    if let (Some(p), Some(n)) = (self.dnf(v, false), self.dnf(v, true)) {
                        if let (Some(gp), Some(gn)) = (and(&guard, &p), and(&guard, &n)) {
                            if !gp.is_empty() {
                                loads.push(Load { guard: gp, val: LoadVal::Const(1), direct: false });
                            }
                            if !gn.is_empty() {
                                loads.push(Load { guard: gn, val: LoadVal::Const(0), direct: false });
                            }
                            return;
                        }
                    }
                }
                // Fusion can fold a value to a constant (e.g. an impossible condition).
                let r = self.rebuild(v);
                match self.g.as_const(r) {
                    Some(k) => LoadVal::Const(k),
                    None => LoadVal::Node(r),
                }
            }
        };
        loads.push(Load { guard, val, direct: false });
    }

    /// Whether `x` is a select tree with `own` (the old value) or a constant among its leaves.
    pub(super) fn mentions(&self, x: V, own: Option<V>) -> bool {
        match self.g.as_mux(x) {
            Some((_, _, a, b)) => [a, b].iter().any(|y| Some(*y) == own || self.g.as_const(*y).is_some() || self.mentions(*y, own)),
            None => false,
        }
    }

    /// Plans a writer's update of a register. `None` if it never changes it.
    pub fn writer_plan(&mut self, next: V, own: Option<V>) -> Option<WriterPlan> {
        let mut loads = self.plan(next, own)?;
        // Constant loads under a condition can check it themselves, if the "none of them
        // fires" condition (needed by the hold decider) stays small.
        let mut union: Option<Dnf> = Some(vec![]);
        let mut any = false;
        for l in &loads {
            if matches!(l.val, LoadVal::Const(_)) && !is_true(&l.guard) {
                any = true;
                union = union.and_then(|u| or(u, l.guard.clone()));
            }
        }
        let keep = if any { union.as_ref().and_then(negate) } else { None };
        if keep.is_some() {
            for l in &mut loads {
                l.direct = matches!(l.val, LoadVal::Const(_)) && !is_true(&l.guard);
            }
        }
        Some(WriterPlan { loads, keep })
    }
}
