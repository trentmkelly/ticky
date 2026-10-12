//! Weighted counts over slots: sums of constant multiples of `b[s] op k` become a
//! domain-restricted filter and a total. Domain values carry the weights, including
//! multiplicities and negative coefficients; missing bundle signals are tested as zero.

use ticky_factorio::{ArOp, CmpOp};

use super::*;
use crate::ir::{BLit, BOp, BTerm, Op, V};

impl Fuser<'_> {
    /// Additive leaves and their coefficients, with all arithmetic modulo 2^32.
    /// Distributing constant multiplication is safe under the same wrapping semantics.
    fn count_leaves(&self, v: V, weight: i32, out: &mut Vec<(V, i32)>, budget: &mut usize) -> bool {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        match *self.g.op(v) {
            Op::Ar(ArOp::Add, x, y) => self.count_leaves(x, weight, out, budget) && self.count_leaves(y, weight, out, budget),
            Op::Ar(ArOp::Sub, x, y) => self.count_leaves(x, weight, out, budget) && self.count_leaves(y, weight.wrapping_neg(), out, budget),
            Op::Ar(ArOp::Mul, x, k) if self.g.as_const(k).is_some() => {
                self.count_leaves(x, weight.wrapping_mul(self.g.as_const(k).unwrap()), out, budget)
            }
            _ => {
                out.push((v, weight));
                true
            }
        }
    }

    /// `bundle[s] op k` (either way round), normalized to the bundle on the left.
    fn slot_test(&self, v: V) -> Option<(V, ticky_factorio::Sig, CmpOp, i32)> {
        let Op::Cmp(op, a, b) = *self.g.op(v) else { return None };
        let (x, op, k) = match (self.g.as_const(a), self.g.as_const(b)) {
            (None, Some(k)) => (a, op, k),
            (Some(k), None) => (b, op.flip(), k),
            _ => return None,
        };
        match *self.g.op(x) {
            Op::BGet(bun, s) => Some((bun, s, op, k)),
            _ => None,
        }
    }

    /// A weighted sum of slot predicates becomes a filter of a constant weight table.
    /// The filter iterates only listed signals (a missing bundle signal reads zero),
    /// copies their weights, and its total can be emitted by that same decider.
    pub(super) fn count_sum(&mut self, v: V) -> Option<V> {
        let mut leaves = Vec::new();
        if !self.count_leaves(v, 1, &mut leaves, &mut 192) {
            return None;
        }
        // (bundle, comparison, constant) -> [(leaf index, signal, weight)]
        let mut groups: Vec<((V, CmpOp, i32), Vec<(usize, ticky_factorio::Sig, i32)>)> = Vec::new();
        for (i, &(l, w)) in leaves.iter().enumerate() {
            let Some((b, s, op, k)) = self.slot_test(l) else { continue };
            match groups.iter_mut().find(|(key, _)| *key == (b, op, k)) {
                Some((_, v)) => v.push((i, s, w)),
                None => groups.push(((b, op, k), vec![(i, s, w)])),
            }
        }
        // Preserve the established threshold; lookup cost selection is separate.
        groups.retain(|(_, v)| v.len() >= 3);
        if groups.is_empty() {
            return None;
        }
        let mut used = vec![false; leaves.len()];
        let mut terms = Vec::new();
        for ((b, op, k), members) in groups {
            for (i, _, _) in &members {
                used[*i] = true;
            }
            let b = self.rebuild(b);
            // bconst adds repeated signals with wrapping arithmetic and omits zero weights.
            let dom = self.g.bconst(members.iter().map(|(_, s, w)| (*s, *w)));
            if self.g.as_bconst(dom).is_some_and(|vals| vals.is_empty()) {
                terms.push(self.g.konst(0));
                continue;
            }
            let kv = self.g.konst(k);
            let cond = vec![vec![BLit { op, a: BOp::Each, b: BOp::Val(kv) }]];
            let hits = self.g.bun(vec![BTerm::DFilter(dom, b, cond, crate::ir::FOut::Copy)]);
            terms.push(self.g.btotal(hits));
        }
        for (i, (l, w)) in leaves.into_iter().enumerate() {
            if !used[i] {
                let l = self.rebuild(l);
                let w = self.g.konst(w);
                terms.push(self.g.ar(ArOp::Mul, l, w));
            }
        }
        let mut acc = terms[0];
        for &t in &terms[1..] {
            acc = self.g.ar(ArOp::Add, acc, t);
        }
        Some(acc)
    }
}
