//! Table lookups: one-hot `Bun` arms all testing `x == c_i` (≥3) → a constant table and one
//! `Hot` decider ([`Fuser::table_lookups`], from `rebuild` of a `Bun`).

use ticky_factorio::CmpOp;

use super::*;
use crate::ir::{BTerm, Lit, V};

impl Fuser<'_> {
    /// One-hot outputs picked by comparing one scalar with constants (`A if x == 1 else B if
    /// x == 2 else …`, a decider per arm) become a table lookup: a constant table of the
    /// arms' values and one decider passing the signal whose value equals `x` (a [`BTerm::Hot`],
    /// plus the index signal; the table is shared by equal lookups).
    pub(super) fn table_lookups(&mut self, terms: Vec<BTerm>) -> Vec<BTerm> {
        // x → [(term index, constant, signal)]
        let mut groups: Vec<(V, Vec<(usize, i32, ticky_factorio::Sig)>)> = Vec::new();
        for (i, t) in terms.iter().enumerate() {
            let BTerm::Dec(arms) = t else { continue };
            let [(d, vals)] = arms.as_slice() else { continue };
            let ([term], [(sig, 1)]) = (d.as_slice(), vals.as_slice()) else { continue };
            let side = |l: &Lit| match (self.g.as_const(l.a), self.g.as_const(l.b)) {
                (None, Some(k)) => Some((l.a, k)),
                (Some(k), None) => Some((l.b, k)),
                _ => None,
            };
            let eqs: Vec<(V, i32)> = term.iter().filter(|l| l.op == CmpOp::Eq).filter_map(side).collect();
            let [(x, c)] = eqs.as_slice() else { continue };
            // Anything else must be `x != c'` for another constant: implied by `x == c`.
            let implied = term.iter().all(|l| match (l.op, side(l)) {
                (CmpOp::Eq, Some((y, k))) => y == *x && k == *c,
                (CmpOp::Ne, Some((y, k))) => y == *x && k != *c,
                _ => false,
            });
            if !implied {
                continue;
            }
            match groups.iter_mut().find(|(y, _)| y == x) {
                Some((_, v)) => v.push((i, *c, *sig)),
                None => groups.push((*x, vec![(i, *c, *sig)])),
            }
        }
        let mut drop = vec![false; terms.len()];
        let mut extra = Vec::new();
        for (x, arms) in groups {
            let distinct = |f: &dyn Fn(&(usize, i32, ticky_factorio::Sig)) -> i64| {
                let mut v: Vec<i64> = arms.iter().map(f).collect();
                v.sort();
                v.dedup();
                v.len() == arms.len()
            };
            // Worth it from three arms (index, table and lookup against a decider per arm).
            if arms.len() < 3 || !distinct(&|a| a.1 as i64) || !distinct(&|a| a.2 .0 as i64) {
                continue;
            }
            // Table values must be non-zero (a constant combinator can't hold 0): shift them,
            // and the index with them, when an arm compares with 0.
            let k: i64 = if arms.iter().any(|a| a.1 == 0) { 1 - arms.iter().map(|a| a.1 as i64).min().unwrap() } else { 0 };
            if arms.iter().any(|a| (a.1 as i64 + k) > i32::MAX as i64 || (a.1 as i64 + k) == 0) {
                continue;
            }
            let table = self.g.bconst(arms.iter().map(|a| (a.2, (a.1 as i64 + k) as i32)));
            let idx = ticky_factorio::SignalTable::base().index_signal();
            let ix = self.g.bun(vec![BTerm::Shift(idx, x, k as i32)]);
            for a in &arms {
                drop[a.0] = true;
            }
            extra.push(BTerm::Hot(table, ix, 1));
        }
        terms.into_iter().zip(drop).filter(|(_, d)| !d).map(|(t, _)| t).chain(extra).collect()
    }
}
