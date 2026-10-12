//! Sorting networks and order statistics: a tree of `min`/`max` (or of compare-and-swaps,
//! `y if x > y else x`) → selector combinators ranking the leaves. Mixed networks use
//! up to 16 leaves; homogeneous min/max reductions can fill the available signal pool.
//! [`Fuser::plan_order_stats`] (called with a block's or program's roots before anything is
//! rebuilt) chooses which nodes, [`Fuser::order_stat`] (from `rebuild`) builds them.
//!
//! A function built only from `min` and `max` commutes with every monotone map, so it is
//! fixed by its values on 0/1 inputs (the 0-1 principle): if those are "at least m ones",
//! it is the (n-m)-th smallest leaf, ties included, over all i32 values. The tree is
//! evaluated on all 2^n 0/1 inputs at once (one bit per input), and only replaced when it
//! is such a threshold function. Unused outputs of a hand-written sort then cost nothing.

use std::collections::{BTreeSet, HashMap};

use ticky_factorio::{CmpOp, Sig};

use super::*;
use crate::ir::{BLit, BOp, BTerm, FOut, Op, V};

/// Most leaves of a tree evaluated (2^16 inputs: 1024 words per node).
const MAX_LEAVES: usize = 16;
/// Most `min`/`max` nodes looked at under one root.
const MAX_NODES: usize = 256;
/// Half combinators a replacement must save beyond its estimated cost: small trees (a
/// `min` of three) are close calls the estimate can get wrong.
const MARGIN: usize = 6;

/// The leaves of a min/max tree (sorted) and how many min/max nodes it has.
struct Tree {
    leaves: Vec<V>,
    nodes: usize,
}

impl Fuser<'_> {
    /// `v` as `min(p, q)` / `max(p, q)`: `(p, q, is_max)`. Only the exact select shape: a
    /// comparison of `p` and `q`, its negation, and the arms `p` and `q`. Equal values make
    /// either arm right, so `<`/`<=` and `>`/`>=` all qualify.
    fn min_max(&self, v: V) -> Option<(V, V, bool)> {
        let g = &self.g;
        let Op::Mux { t, f, a, b } = *g.op(v) else { return None };
        let Op::Cmp(op, p, q) = *g.op(t) else { return None };
        if !matches!(op, CmpOp::Lt | CmpOp::Le | CmpOp::Gt | CmpOp::Ge) {
            return None;
        }
        match *g.op(f) {
            Op::Cmp(nop, np, nq) if nop == op.negate() && (np, nq) == (p, q) => {}
            _ => return None,
        }
        if g.is_bundle(p) || g.is_bundle(q) {
            return None;
        }
        // `p > q ? p : q` is the larger.
        let picks_p = if (a, b) == (p, q) {
            true
        } else if (a, b) == (q, p) {
            false
        } else {
            return None;
        };
        let p_larger = matches!(op, CmpOp::Gt | CmpOp::Ge);
        Some((p, q, picks_p == p_larger))
    }

    /// The leaves and size of the min/max tree under `v` (within the caps).
    fn min_max_tree(&self, v: V) -> Option<Tree> {
        let mut leaves = Vec::new();
        let mut seen = BTreeSet::new();
        let mut stack = vec![v];
        let mut nodes = 0;
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            match self.min_max(x) {
                Some((p, q, _)) => {
                    nodes += 1;
                    if nodes > MAX_NODES {
                        return None;
                    }
                    stack.push(p);
                    stack.push(q);
                }
                None => {
                    leaves.push(x);
                    if leaves.len() > MAX_LEAVES {
                        return None;
                    }
                }
            }
        }
        leaves.sort();
        Some(Tree { leaves, nodes })
    }

    /// If the min/max tree under `v` is an order statistic of its leaves: the leaves and the
    /// rank `k` (0 = smallest).
    fn order_stat_of(&self, v: V) -> Option<(Vec<V>, usize)> {
        let tree = match self.min_max_tree(v) {
            Some(tree) => tree,
            None => return self.large_extremum(v),
        };
        let n = tree.leaves.len();
        if tree.nodes < 2 || n < 3 {
            return None;
        }
        // Truth tables: bit `x` of a node's table is its value on input `x` (leaf `i` = bit
        // `i` of `x`). min is AND, max is OR.
        let words = (1usize << n).div_ceil(64);
        let mask = if n < 6 { (1u64 << (1 << n)) - 1 } else { !0 };
        let mut tables: HashMap<V, Vec<u64>> = HashMap::new();
        for (i, &l) in tree.leaves.iter().enumerate() {
            let t = (0..words)
                .map(|w| {
                    let mut bits = 0u64;
                    for j in 0..64.min(1usize << n) {
                        if ((w * 64 + j) >> i) & 1 == 1 {
                            bits |= 1 << j;
                        }
                    }
                    bits
                })
                .collect();
            tables.insert(l, t);
        }
        let table = self.truth_table(v, &mut tables, words);
        // The threshold: the fewest ones among inputs giving 1.
        let m = (0..1usize << n).filter(|x| table[x / 64] >> (x % 64) & 1 == 1).map(|x| x.count_ones() as usize).min()?;
        let ok = (0..words).all(|w| {
            let mut want = 0u64;
            for j in 0..64.min(1usize << n) {
                if ((w * 64 + j).count_ones() as usize) >= m {
                    want |= 1 << j;
                }
            }
            table[w] & mask == want & mask
        });
        ok.then_some((tree.leaves, n - m))
    }

    /// Associativity/idempotence prove a homogeneous reduction without a truth table.
    /// Only homogeneous trees qualify; distinct leaves need distinct wire signals.
    fn large_extremum(&self, v: V) -> Option<(Vec<V>, usize)> {
        let (_, _, max) = self.min_max(v)?;
        let capacity = ticky_factorio::SignalTable::base().internal_pool().len();
        let mut seen = BTreeSet::new();
        let mut leaves = BTreeSet::new();
        let mut stack = vec![v];
        while let Some(x) = stack.pop() {
            if !seen.insert(x) {
                continue;
            }
            match self.min_max(x) {
                Some((p, q, kind)) if kind == max => stack.extend([p, q]),
                Some(_) => return None,
                None => {
                    leaves.insert(x);
                    if leaves.len() > capacity {
                        return None;
                    }
                }
            }
        }
        if leaves.len() < 3 {
            return None;
        }
        let k = if max { leaves.len() - 1 } else { 0 };
        Some((leaves.into_iter().collect(), k))
    }

    fn truth_table(&self, v: V, tables: &mut HashMap<V, Vec<u64>>, words: usize) -> Vec<u64> {
        if let Some(t) = tables.get(&v) {
            return t.clone();
        }
        let (p, q, max) = self.min_max(v).expect("inner nodes are min/max");
        let (tp, tq) = (self.truth_table(p, tables, words), self.truth_table(q, tables, words));
        let t: Vec<u64> = tp.iter().zip(&tq).map(|(a, b)| if max { a | b } else { a & b }).collect();
        tables.insert(v, t.clone());
        t
    }

    /// The leaves as one bundle, each on its own signal (rebuilt): the listed signals of a
    /// bundle when every leaf reads a different signal of it, else one signal per leaf.
    fn leaf_bundle(&mut self, leaves: &[V]) -> V {
        let reads: Option<Vec<(V, Sig)>> = leaves
            .iter()
            .map(|&l| match *self.g.op(l) {
                Op::BGet(b, s) => Some((b, s)),
                _ => None,
            })
            .collect();
        if let Some(reads) = reads {
            let b = reads[0].0;
            let sigs: BTreeSet<Sig> = reads.iter().map(|r| r.1).collect();
            if reads.iter().all(|r| r.0 == b) && sigs.len() == reads.len() {
                let b = self.rebuild(b);
                // The listed signals of `b`: a decider iterating `b` and a constant mask.
                let ones = self.g.bconst(sigs.iter().map(|s| (*s, 1)));
                let z = self.g.konst(0);
                let listed = vec![vec![BLit { op: CmpOp::Ne, a: BOp::Each, b: BOp::Val(z) }]];
                return self.g.bun(vec![BTerm::DFilter(b, ones, listed, FOut::Copy)]);
            }
        }
        let t = ticky_factorio::SignalTable::base();
        let mut pool = t.internal_pool();
        pool.sort_by_key(|s| t.rank(*s));
        let terms: Vec<BTerm> = leaves
            .iter()
            .zip(pool)
            .map(|(&l, sig)| {
                let x = self.rebuild(l);
                self.rebuild_term(BTerm::One(sig, x))
            })
            .collect();
        self.g.bun(terms)
    }

    /// Chooses the order statistics to build, given everything the code needs (`roots`):
    /// the min/max nodes read by something other than another min/max (a network's
    /// outputs) or needed themselves, that are order statistics, when replacing them saves
    /// combinators. Until this runs, nothing is replaced.
    ///
    /// Costs, in half combinators (tuned on random networks): a min/max select 2 (two
    /// deciders), 3.5 in a pipelined block (its operands are delayed to match), each of its
    /// two comparisons 1 (a swap's two selects share them); a rank 5 (two selectors, two
    /// filters, a total), or 2 when the leaves are never negative or never positive; and
    /// gathering the leaves into one bundle. A node is saved when everything reading it is
    /// saved or replaced. Try all candidates, then independent groups and bounded subsets;
    /// every choice must beat a [`MARGIN`].
    pub fn plan_order_stats(&mut self, roots: &[V], pipelined: bool) {
        // A pipelined select also needs its operands delayed to match.
        let (w_mux, w_cmp) = if pipelined { (7, 2) } else { (4, 2) };
        let live = self.g.reachable(roots);
        self.plan_argmax_scores(&live);
        let mut users: HashMap<V, Vec<V>> = HashMap::new();
        for &v in &live {
            for o in self.g.operands(v) {
                users.entry(o).or_default().push(v);
            }
        }
        let mut conds = BTreeSet::new();
        for &v in &live {
            if let (Some(_), Op::Mux { t, f, .. }) = (self.min_max(v), self.g.op(v)) {
                conds.extend([*t, *f]);
            }
        }
        let network = |this: &Self, u: V| conds.contains(&u) || this.min_max(u).is_some();
        // An output that isn't an order statistic may still be built from some: the
        // largest order statistics under it are candidates too.
        let mut cands: Vec<(V, Vec<V>, usize)> = Vec::new();
        let mut stack: Vec<V> = live
            .iter()
            .copied()
            .filter(|&v| self.min_max(v).is_some() && (roots.contains(&v) || users.get(&v).is_some_and(|us| us.iter().any(|&u| !network(self, u)))))
            .collect();
        let mut seen = BTreeSet::new();
        while let Some(v) = stack.pop() {
            let Some((p, q, _)) = self.min_max(v) else { continue };
            if !seen.insert(v) {
                continue;
            }
            match self.order_stat_of(v) {
                Some((leaves, k)) => cands.push((v, leaves, k)),
                None => stack.extend([p, q]),
            }
        }
        cands.sort_by_key(|c| c.0);
        let gain_of = |this: &Self, chosen: &[&(V, Vec<V>, usize)]| -> isize {
            // The trees' selects and their comparisons, newest (readers) first.
            let mut nodes = BTreeSet::new();
            for (v, ..) in chosen {
                let mut stack = vec![*v];
                while let Some(x) = stack.pop() {
                    if let (Some((p, q, _)), Op::Mux { t, f, .. }) = (this.min_max(x), this.g.op(x)) {
                        if nodes.insert(x) {
                            nodes.extend([*t, *f]);
                            stack.extend([p, q]);
                        }
                    }
                }
            }
            let replaced: BTreeSet<V> = chosen.iter().map(|c| c.0).collect();
            let mut saved = BTreeSet::new();
            let mut gain = 0;
            for &x in nodes.iter().rev() {
                let unread = || !roots.contains(&x) && users.get(&x).is_none_or(|us| us.iter().all(|u| saved.contains(u)));
                if replaced.contains(&x) || unread() {
                    saved.insert(x);
                    gain += if conds.contains(&x) { w_cmp } else { w_mux };
                }
            }
            let mut cost = 0;
            let mut gathered = BTreeSet::new();
            for (_, leaves, _) in chosen {
                cost += if this.one_sided(leaves) || this.all_nonzero(leaves) { 4 } else { 10 };
                if gathered.insert(leaves.clone()) {
                    cost += 2 * this.gather_cost(leaves);
                }
            }
            if std::env::var_os("TICKY_DUMP_SORTNET").is_some() {
                let outs: Vec<String> = chosen.iter().map(|(v, l, k)| format!("%{v} = rank {k} of {}", l.len())).collect();
                eprintln!("order statistics [{}]: saves {gain}/2, costs {cost}/2", outs.join(", "));
            }
            gain as isize - cost as isize
        };
        let all: Vec<_> = cands.iter().collect();
        let chosen: Vec<_> = if gain_of(self, &all) > MARGIN as isize {
            all
        } else {
            // Independent networks should not subsidize one another. Connect candidates
            // sharing removable nodes or a gather, then consider subsets in small groups.
            let nodes: Vec<BTreeSet<V>> = cands.iter().map(|(v, ..)| {
                let mut found = BTreeSet::new();
                let mut stack = vec![*v];
                while let Some(x) = stack.pop() {
                    if let Some((p, q, _)) = self.min_max(x) {
                        if found.insert(x) {
                            if let Op::Mux { t, f, .. } = *self.g.op(x) {
                                found.extend([t, f]);
                            }
                            stack.extend([p, q]);
                        }
                    }
                }
                found
            }).collect();
            let mut groups: Vec<Vec<usize>> = Vec::new();
            for i in 0..cands.len() {
                let mut group = vec![i];
                let mut j = 0;
                while j < groups.len() {
                    if groups[j].iter().any(|&k| cands[i].1 == cands[k].1 || !nodes[i].is_disjoint(&nodes[k])) {
                        group.extend(groups.remove(j));
                    } else {
                        j += 1;
                    }
                }
                group.sort_unstable();
                groups.push(group);
            }
            let mut chosen = Vec::new();
            for group in groups {
                let whole: Vec<_> = group.iter().map(|&i| &cands[i]).collect();
                if gain_of(self, &whole) > MARGIN as isize {
                    chosen.extend(whole);
                } else if group.len() <= 8 {
                    let mut best = Vec::new();
                    let mut best_gain = MARGIN as isize;
                    for mask in 1..(1usize << group.len()) {
                        let subset: Vec<_> = group.iter().enumerate().filter(|(j, _)| mask & (1 << j) != 0).map(|(_, &i)| &cands[i]).collect();
                        let gain = gain_of(self, &subset);
                        if gain > best_gain {
                            best_gain = gain;
                            best = subset;
                        }
                    }
                    chosen.extend(best);
                } else {
                    // Keep compilation bounded on many-output networks.
                    chosen.extend(whole.into_iter().filter(|c| gain_of(self, &[*c]) > MARGIN as isize));
                }
            }
            chosen
        };
        self.order_stats = chosen.into_iter().map(|(v, leaves, k)| (*v, (leaves.clone(), *k))).collect();
    }

    /// Whether the leaves are never negative or never positive (one selector does).
    fn one_sided(&self, leaves: &[V]) -> bool {
        leaves.iter().all(|&l| self.g.iv(l).lo >= 0) || leaves.iter().all(|&l| self.g.iv(l).hi <= 0)
    }

    /// All leaves are present on the wire, even when their signs differ.
    fn all_nonzero(&self, leaves: &[V]) -> bool {
        leaves.iter().all(|&l| {
            let iv = self.g.iv(l);
            iv.lo > 0 || iv.hi < 0
        })
    }

    /// Combinators [`leaf_bundle`](Self::leaf_bundle) adds, about.
    fn gather_cost(&self, leaves: &[V]) -> usize {
        let b = match self.g.op(leaves[0]) {
            Op::BGet(b, _) => Some(*b),
            _ => None,
        };
        if b.is_some() && leaves.iter().all(|&l| matches!(*self.g.op(l), Op::BGet(x, _) if Some(x) == b)) {
            return 2;
        }
        let consts = leaves.iter().filter(|&&l| self.g.as_const(l).is_some()).count();
        leaves.len() - consts + (consts > 0) as usize
    }

    /// [`order_stat_of`](Self::order_stat_of) built from selector combinators. A selector
    /// ranks the signals on its wire, and a leaf that is 0 isn't there: zeros sit between the
    /// negative and the positive leaves. So the k-th smallest is the k-th smallest present
    /// signal if that is negative, else the (n-1-k)-th largest if that is positive, else 0
    /// (at most one of the two holds). With leaves never negative (or never positive) one
    /// selector does.
    pub(super) fn order_stat(&mut self, v: V) -> Option<V> {
        let (leaves, k) = self.order_stats.get(&v)?.clone();
        let n = leaves.len();
        let nonneg = leaves.iter().all(|&l| self.g.iv(l).lo >= 0);
        let nonpos = leaves.iter().all(|&l| self.g.iv(l).hi <= 0);
        let keys = self.leaf_bundle(&leaves);
        let z = self.g.konst(0);
        let lo = self.g.brank(keys, false, k as u32);
        let hi = self.g.brank(keys, true, (n - 1 - k) as u32);
        if self.all_nonzero(&leaves) {
            return Some(self.g.btotal(lo));
        }
        if nonneg {
            return Some(self.g.btotal(hi));
        }
        if nonpos {
            return Some(self.g.btotal(lo));
        }
        let only = |op| vec![vec![BLit { op, a: BOp::Each, b: BOp::Val(z) }]];
        let both = self.g.bun(vec![BTerm::Filter(lo, only(CmpOp::Lt), FOut::Copy), BTerm::Filter(hi, only(CmpOp::Gt), FOut::Copy)]);
        Some(self.g.btotal(both))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::{Graph, Iv};

    #[test]
    fn rank_paths_preserve_zeros_duplicates_and_i32_extremes() {
        for values in [
            [i32::MIN, -1, 1, i32::MAX],
            [-5, -5, 1, 1],
            [0, -5, 0, 3],
            [0, 0, 0, 0],
            [0, 1, 1, i32::MAX],
            [i32::MIN, -1, -1, 0],
        ] {
            let mut expected = values;
            expected.sort_unstable();
            for rotation in 0..values.len() {
                let mut input = values;
                input.rotate_left(rotation);
                for (rank, &want) in expected.iter().enumerate() {
                    let mut g = Graph::default();
                    let leaves = input.iter().map(|&v| g.konst(v)).collect();
                    let root = g.konst(12345);
                    let mut f = Fuser::new(&mut g);
                    f.order_stats.insert(root, (leaves, rank));
                    let out = f.order_stat(root).unwrap();
                    assert_eq!(f.g.as_const(out), Some(want), "rank {rank} of {input:?}");
                }
            }
        }
    }

    #[test]
    fn mixed_sign_nonzero_rank_needs_one_selector() {
        let mut g = Graph::new(vec![Iv { lo: -20, hi: -1 }, Iv { lo: 1, hi: 20 }, Iv { lo: 2, hi: 30 }]);
        let leaves: Vec<_> = (0..3).map(|i| g.src(i)).collect();
        let root = g.konst(12345);
        let mut f = Fuser::new(&mut g);
        f.order_stats.insert(root, (leaves, 1));
        let out = f.order_stat(root).unwrap();
        let live = f.g.reachable(&[out]);
        assert_eq!(live.iter().filter(|&&v| matches!(f.g.op(v), Op::BSelect(_, false, 1))).count(), 1);
        assert_eq!(live.iter().filter(|&&v| matches!(f.g.op(v), Op::BSelect(..))).count(), 1);
        assert!(matches!(f.g.op(out), Op::BTotal(_)));
    }
}
