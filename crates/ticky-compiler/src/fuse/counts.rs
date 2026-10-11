//! Counting matches over slots: `(b[s1] == k) + (b[s2] == k) + …` (≥3 terms, same `b` and
//! `k`) → one domain-restricted filter and a total ([`Fuser::count_sum`], from `rebuild` of
//! an `Add`).

use ticky_factorio::{ArOp, CmpOp};

use super::*;
use crate::ir::{BLit, BOp, BTerm, Op, V};

impl Fuser<'_> {
    /// The leaves of a tree of `+` (original nodes), at most `limit` of them.
    pub(super) fn add_leaves(&self, v: V, out: &mut Vec<V>, limit: usize) -> bool {
        if out.len() > limit {
            return false;
        }
        match *self.g.op(v) {
            Op::Ar(ArOp::Add, x, y) => self.add_leaves(x, out, limit) && self.add_leaves(y, out, limit),
            _ => {
                out.push(v);
                true
            }
        }
    }

    /// `bundle[s] == k` (either way round): `(bundle, s, k)`.
    pub(super) fn slot_test(&self, v: V) -> Option<(V, ticky_factorio::Sig, i32)> {
        let Op::Cmp(CmpOp::Eq, a, b) = *self.g.op(v) else { return None };
        let (x, k) = match (self.g.as_const(a), self.g.as_const(b)) {
            (None, Some(k)) => (a, k),
            (Some(k), None) => (b, k),
            _ => return None,
        };
        match *self.g.op(x) {
            Op::BGet(bun, s) => Some((bun, s, k)),
            _ => None,
        }
    }

    /// A sum counting matches, `(b[s1] == k) + (b[s2] == k) + …` (an array's elements equal
    /// to a constant, say), from three terms on: one filter over those signals of `b` and
    /// one total, instead of a comparison per term. The filter iterates the listed signals
    /// (a missing one reads 0), so other signals on `b`'s wire don't count.
    pub(super) fn count_sum(&mut self, v: V) -> Option<V> {
        let mut leaves = Vec::new();
        if !self.add_leaves(v, &mut leaves, 64) {
            return None;
        }
        // (bundle, k) → [(leaf index, signal)]
        let mut groups: Vec<((V, i32), Vec<(usize, ticky_factorio::Sig)>)> = Vec::new();
        for (i, &l) in leaves.iter().enumerate() {
            let Some((b, s, k)) = self.slot_test(l) else { continue };
            match groups.iter_mut().find(|(key, _)| *key == (b, k)) {
                Some((_, v)) if !v.iter().any(|(_, t)| *t == s) => v.push((i, s)),
                Some(_) => {}
                None => groups.push(((b, k), vec![(i, s)])),
            }
        }
        groups.retain(|(_, v)| v.len() >= 3);
        if groups.is_empty() {
            return None;
        }
        let mut used = vec![false; leaves.len()];
        let mut terms = Vec::new();
        for ((b, k), members) in groups {
            for (i, _) in &members {
                used[*i] = true;
            }
            let b = self.rebuild(b);
            let dom = self.g.bconst(members.iter().map(|(_, s)| (*s, 1)));
            let kv = self.g.konst(k);
            let cond = vec![vec![BLit { op: CmpOp::Eq, a: BOp::Each, b: BOp::Val(kv) }]];
            let hits = self.g.bun(vec![BTerm::DFilter(dom, b, cond, crate::ir::FOut::Copy)]);
            terms.push(self.g.btotal(hits));
        }
        for (i, l) in leaves.into_iter().enumerate() {
            if !used[i] {
                terms.push(self.rebuild(l));
            }
        }
        let mut acc = terms[0];
        for &t in &terms[1..] {
            acc = self.g.ar(ArOp::Add, acc, t);
        }
        Some(acc)
    }
}
