//! Table lookups: one-hot `Bun` arms all testing `x == c_i` → a constant table and one
//! `HotEq` (or, shifted off 0, `Hot`) decider ([`Fuser::table_lookups`], from `rebuild` of a
//! `Bun`). Also: a runtime pick among reads of one bundle → a lookup of the signal and one
//! `b · onehot` ([`Fuser::picked_read`], from `rebuild` of a `Sel`), and one-hot lookups
//! sharing an existing index wire ([`Fuser::shared_hot_index`]).

use ticky_factorio::CmpOp;

use super::*;
use crate::ir::{BTerm, Lit, Op, V};

/// Choose an additive encoding with no zero table entries. Wrapping addition is a
/// permutation of all i32 values, so it preserves equality even across signed overflow.
/// With N keys, at most N offsets are forbidden; one of 0..=N must work.
fn key_offset(keys: impl Iterator<Item = i32>) -> i32 {
    let forbidden: std::collections::HashSet<i32> = keys.map(i32::wrapping_neg).collect();
    (0..=forbidden.len()).map(|k| k as i32).find(|k| !forbidden.contains(k)).unwrap()
}

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
            if arms.len() < 2 || !distinct(&|a| a.1 as i64) || !distinct(&|a| a.2 .0 as i64) {
                continue;
            }
            // Count active combinators, as the benchmark does: HotEq needs one, whereas
            // Hot needs an index shift as well. A two-arm shifted table would only tie.
            let k = key_offset(arms.iter().map(|a| a.1));
            let cost = if k == 0 { 1 } else { 2 };
            if arms.len() <= cost {
                continue;
            }
            let table = self.g.bconst(arms.iter().map(|a| (a.2, a.1.wrapping_add(k))));
            for a in &arms {
                drop[a.0] = true;
            }
            // Unshifted, the decider compares the table with `x` itself (no index wire).
            if k == 0 {
                extra.push(BTerm::HotEq(table, x, 1));
                continue;
            }
            let idx = ticky_factorio::SignalTable::base().index_signal();
            let ix = self.g.bun(vec![BTerm::Shift(idx, x, k)]);
            extra.push(BTerm::Hot(table, ix, 1));
        }
        terms.into_iter().zip(drop).filter(|(_, d)| !d).map(|(t, _)| t).chain(extra).collect()
    }

    /// `[b[s_0], b[s_1], …][x]` (a select of reads of one bundle, arm `i` taken when
    /// `x == c_i`), from three arms: a lookup of `x` in a table of the signals and one
    /// `b · onehot` arithmetic, instead of a read, a comparison and a select per arm. The
    /// lookup reuses an index wire `x + k` that the block already has (an array access by the
    /// same `x`, say) when that keeps the table off 0.
    pub(super) fn picked_read(&mut self, v: V) -> Option<V> {
        let Op::Sel(arms) = self.g.op(v).clone() else { return None };
        if arms.len() < 3 {
            return None;
        }
        let mut x0 = None;
        let mut bun = None;
        let mut picks: Vec<(i32, ticky_factorio::Sig)> = Vec::new();
        for (c, val) in arms {
            let Op::Cmp(CmpOp::Eq, a, b) = *self.g.op(c) else { return None };
            let (x, k) = match (self.g.as_const(a), self.g.as_const(b)) {
                (None, Some(k)) => (a, k),
                (Some(k), None) => (b, k),
                _ => return None,
            };
            let Op::BGet(bv, s) = *self.g.op(val) else { return None };
            if *x0.get_or_insert(x) != x || *bun.get_or_insert(bv) != bv || picks.iter().any(|p| p.0 == k || p.1 == s) {
                return None;
            }
            picks.push((k, s));
        }
        let (x, b) = (self.rebuild(x0?), self.rebuild(bun?));
        let fits = |k: i32| picks.iter().all(|p| p.0.wrapping_add(k) != 0);
        let table = |g: &mut crate::ir::Graph, k: i32| g.bconst(picks.iter().map(|p| (p.1, p.0.wrapping_add(k))));
        let hot = match self.index_wire(x0?, x, &fits) {
            Some((ix, k)) => {
                let t = table(self.g, k);
                self.g.bun(vec![BTerm::Hot(t, ix, 1)])
            }
            None if fits(0) => {
                let t = table(self.g, 0);
                self.g.bun(vec![BTerm::HotEq(t, x, 1)])
            }
            None => {
                let k = key_offset(picks.iter().map(|p| p.0));
                let t = table(self.g, k);
                let idx = ticky_factorio::SignalTable::base().index_signal();
                let ix = self.g.bun(vec![BTerm::Shift(idx, x, k)]);
                self.g.bun(vec![BTerm::Hot(t, ix, 1)])
            }
        };
        Some(self.g.bdot(b, hot))
    }

    /// An index bundle of the block holding `x + k` on the index signal (one `Shift` term,
    /// plus any constant terms: an array read's positions) with `ok(k)`, rebuilt, and `k`.
    /// `x` is given as written (`x0`) and rebuilt (`x`); array accesses come first.
    fn index_wire(&mut self, x0: V, x: V, ok: &dyn Fn(i32) -> bool) -> Option<(V, i32)> {
        let idx = ticky_factorio::SignalTable::base().index_signal();
        let mut best: Option<(V, i32, bool)> = None;
        for (i, op) in self.g.nodes.iter().enumerate() {
            let Op::Bun(terms) = op else { continue };
            let mut shift = None;
            let mut konst = false;
            for t in terms {
                match t {
                    BTerm::Shift(s, y, k) if *s == idx && (*y == x0 || *y == x) && shift.is_none() => shift = Some(*k),
                    BTerm::K(_) => konst = true,
                    _ => {
                        shift = None;
                        break;
                    }
                }
            }
            let Some(k) = shift.filter(|k| ok(*k)) else { continue };
            if terms.iter().filter(|t| matches!(t, BTerm::Shift(..))).count() != 1 {
                continue;
            }
            if best.is_none_or(|b| konst && !b.2) {
                best = Some((i as V, k, konst));
            }
        }
        let (ix, k, _) = best?;
        Some((self.rebuild(ix), k))
    }

    /// The index bundle for a one-hot lookup `Hot(t, ix)` with `ix = x + k` alone: an
    /// array read's index bundle for the same `x + k` instead, if the block has one (`aset`
    /// and `aget` by the same index then share the index arithmetic).
    pub(super) fn shared_hot_index(&mut self, ix: V) -> V {
        if let Op::Bun(terms) = self.g.op(ix).clone() {
            if let [BTerm::Shift(_, x0, k)] = terms.as_slice() {
                let x = self.rebuild(*x0);
                if let Some((shared, _)) = self.index_wire(*x0, x, &|c| c == *k) {
                    return shared;
                }
            }
        }
        self.rebuild(ix)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn picked_reads_can_encode_minimum_and_wrapping_keys() {
        for keys in [[i32::MIN, 1, i32::MAX], [i32::MIN, 0, i32::MAX]] {
            let mut g = Graph::new(vec![Iv::FULL, Iv::FULL]);
            g.src_bun = vec![false, true];
            let x = g.src(0);
            let b = g.src(1);
            let mut arms = Vec::new();
            for (i, &k) in keys.iter().enumerate() {
                let k = g.konst(k);
                let cond = g.cmp(CmpOp::Eq, x, k);
                let value = g.bget(b, Graph::slot(i));
                arms.push((cond, value));
            }
            let pick = g.sel(arms);
            let result = Fuser::new(&mut g).picked_read(pick).expect("keys can be encoded without zero");
            let Op::BDot(_, hot) = *g.op(result) else { panic!("expected dot product") };
            let Op::Bun(terms) = g.op(hot) else { panic!("expected one-hot bundle") };
            let (table, offset) = match terms.as_slice() {
                [BTerm::HotEq(t, _, _)] => (*t, 0),
                [BTerm::Hot(t, ix, _)] => {
                    let Op::Bun(ts) = g.op(*ix) else { panic!("expected index") };
                    let [BTerm::Shift(_, _, k)] = ts.as_slice() else { panic!("expected shift") };
                    (*t, *k)
                }
                _ => panic!("expected lookup"),
            };
            assert_eq!(offset == 0, !keys.contains(&0));
            let entries = g.as_bconst(table).unwrap();
            for candidate in [i32::MIN, i32::MIN + 1, -2, -1, 0, 1, 2, i32::MAX] {
                for (i, key) in keys.iter().enumerate() {
                    let encoded = entries.iter().find(|(s, _)| *s == Graph::slot(i)).unwrap().1;
                    assert_ne!(encoded, 0);
                    assert_eq!(candidate == *key, candidate.wrapping_add(offset) == encoded);
                }
            }
        }
    }
}
