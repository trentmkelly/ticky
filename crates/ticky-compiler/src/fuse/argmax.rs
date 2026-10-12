//! Running maximum (`if s_i > top: best, top = K_i, s_i` for ≥3 candidates) → one selector
//! combinator plus a table: [`Fuser::argmax_chain`] recognises it (from `rebuild` and from
//! `split`, for register loads), [`Fuser::argmax`] builds it.

use ticky_factorio::{ArOp, CmpOp};

use super::*;
use crate::ir::{BLit, BOp, BTerm, Op, V};

impl Fuser<'_> {
    /// A running maximum that remembers which candidate won (`best, top = B0, T0`, then
    /// `if s_i > top: best, top = K_i, s_i` for each candidate in turn), seen from the final
    /// `best`: the candidates `(s_i, K_i)` in order, `T0` and `B0`. Strict `>`, so the
    /// earliest of equal maxima wins; three candidates at least; `T0 ≥ 0`.
    pub(super) fn argmax_chain(&self, v: V) -> Option<(Vec<(V, i32)>, i32, i32)> {
        let g = &self.g;
        // `s > top`, either way round: (s, top).
        let gt = |c: V| match *g.op(c) {
            Op::Cmp(CmpOp::Gt, s, t) => Some((s, t)),
            Op::Cmp(CmpOp::Lt, t, s) => Some((s, t)),
            _ => None,
        };
        let mut steps = Vec::new();
        let mut best = v;
        // The `top` the current step compares with must be the previous step's update.
        let mut want_top: Option<(V, V, V)> = None; // (top node, its step's condition, its s)
        loop {
            let (c, k, prev) = match *g.op(best) {
                Op::Mux { t, a, b, .. } => match g.as_const(a) {
                    Some(k) => (t, k, Some(b)),
                    None => return None,
                },
                // `best = 1 if s > top else 0`, simplified to the comparison.
                Op::Cmp(..) => (best, 1, None),
                _ => return None,
            };
            let (s, top) = gt(c)?;
            if let Some((tn, tc, ts)) = want_top {
                match *g.op(tn) {
                    Op::Mux { t, a, b, .. } if t == tc && a == ts && b == top => {}
                    _ => return None,
                }
            }
            steps.push((s, k));
            let prev_best = match prev {
                Some(p) => p,
                None => {
                    // The first step's `best` was folded away: B0 = 0.
                    let t0 = g.as_const(top)?;
                    return (steps.len() >= 3 && t0 >= 0).then(|| {
                        steps.reverse();
                        (steps, t0, 0)
                    });
                }
            };
            if let (Some(b0), Some(t0)) = (g.as_const(prev_best), g.as_const(top)) {
                return (steps.len() >= 3 && t0 >= 0).then(|| {
                    steps.reverse();
                    (steps, t0, b0)
                });
            }
            // The previous `top` is `s_prev if c_prev else top_prev`: checked at the next step.
            let Op::Mux { t: pc, .. } = *g.op(top) else { return None };
            let ps = gt(pc)?.0;
            want_top = Some((top, pc, ps));
            best = prev_best;
        }
    }

    /// Match the score companion before rebuilding either output. Intermediate scores
    /// remain ordinary nodes if other expressions need them.
    pub(super) fn plan_argmax_scores(&mut self, live: &[V]) {
        self.argmax_scores.clear();
        let scores: std::collections::HashMap<_, _> = live.iter().filter_map(|&v| {
            match *self.g.op(v) {
                Op::Mux { t, f, a, b } => Some(((t, f, a, b), v)),
                _ => None,
            }
        }).collect();
        for &best in live {
            if self.argmax_chain(best).is_none() {
                continue;
            }
            let Op::Mux { t, f, .. } = *self.g.op(best) else { continue };
            let (s, prev) = match *self.g.op(t) {
                Op::Cmp(CmpOp::Gt, s, prev) | Op::Cmp(CmpOp::Lt, prev, s) => (s, prev),
                _ => continue,
            };
            if let Some(&top) = scores.get(&(t, f, s, prev)) {
                // The same score can have several label chains. Share one deterministically.
                self.argmax_scores.entry(top).or_insert(best);
            }
        }
    }

    /// [`argmax_chain`](Self::argmax_chain) with a selector combinator: the candidates'
    /// scores on signals ranked in candidate order (so ties go to the earliest, as with
    /// `>`), those above `T0` kept, the largest selected, and its `K` read from a table.
    pub(super) fn argmax(&mut self, steps: Vec<(V, i32)>, top0: i32, best0: i32) -> (V, V) {
        let t = ticky_factorio::SignalTable::base();
        let mut pool = t.internal_pool();
        pool.sort_by_key(|s| t.rank(*s));
        let sigs: Vec<_> = pool.into_iter().take(steps.len()).collect();
        let terms: Vec<BTerm> = steps.iter().zip(&sigs).map(|((s, _), sig)| {
            let x = self.rebuild(*s);
            BTerm::One(*sig, x)
        }).collect();
        let terms = terms.into_iter().map(|t| self.rebuild_term(t)).collect();
        let scores = self.g.bun(terms);
        let k0 = self.g.konst(top0);
        let above = self.g.bun(vec![BTerm::Filter(scores, vec![vec![BLit { op: CmpOp::Gt, a: BOp::Each, b: BOp::Val(k0) }]], crate::ir::FOut::Copy)]);
        let top = self.g.brank(above, true, 0);
        // K_i - B0 on each candidate's signal (a constant combinator can't hold 0: those
        // candidates add nothing, which is right).
        let table = self.g.bconst(steps.iter().zip(&sigs).map(|((_, k), sig)| (*sig, k.wrapping_sub(best0))));
        let z = self.g.konst(0);
        let won = self.g.bun(vec![BTerm::DFilter(table, top, vec![vec![BLit { op: CmpOp::Ne, a: BOp::Each, b: BOp::Val(z) }]], crate::ir::FOut::Copy)]);
        let k = self.g.btotal(won);
        let b0 = self.g.konst(best0);
        let winner = self.g.ar(ArOp::Add, k, b0);
        let score = self.g.btotal(top);
        // Selected scores are strictly positive because T0 >= 0. An empty result
        // therefore has total 0, which must preserve the initial score T0.
        let score = if top0 == 0 {
            score
        } else {
            let present = self.g.cmp(CmpOp::Ne, score, z);
            self.g.mux(present, score, k0)
        };
        (winner, score)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Graph, Iv};

    #[test]
    fn shared_argmax_is_independent_of_root_rebuild_order() {
        for score_first in [true, false] {
            let mut g = Graph::new(vec![Iv::FULL; 4]);
            let mut best = g.konst(0);
            let mut top = best;
            for i in 0..4 {
                let s = g.src(i);
                let c = g.cmp(CmpOp::Gt, s, top);
                let label = g.konst(i as i32 + 11);
                best = g.mux(c, label, best);
                top = g.mux(c, s, top);
            }
            let mut f = Fuser::new(&mut g);
            f.plan_order_stats(&[top, best], true);
            assert_eq!(f.argmax_scores.get(&top), Some(&best));
            let roots = if score_first { [top, best] } else { [best, top] };
            let out = roots.map(|v| f.rebuild(v));
            let live = f.g.reachable(&out);
            assert_eq!(live.iter().filter(|&&v| matches!(f.g.op(v), Op::BSelect(..))).count(), 1);
            let score = f.rebuild(top);
            assert!(matches!(f.g.op(score), Op::BTotal(_)));
        }
    }
}
