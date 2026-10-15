//! Straight-line vectorisation (SLP): scalar operations of the same shape in one block's
//! logic (`a = x * 3`, `b = y * 3`, `c = z * 3`) done by one `each` combinator.
//!
//! Each such operation (a *lane*) reads one value and a constant. The lane's input is
//! written under the lane's own bus signal onto a private wire instead of the bus, and one
//! combinator computes `each op k` over that wire straight onto the bus, where every lane's
//! result is its own signal, exactly where the scalar combinator would have put it. Consumers
//! don't change and no reads are needed: the only cost is the input being redirected, so only
//! inputs that exist just for their lane (single-use combinators) qualify.
//!
//! Lanes need not be independent: the combinator treats every signal separately, so a lane
//! feeding another lane's input through other logic is fine (it settles one tick per
//! combinator, like the scalar version).
//!
//! Forms, by what a missing signal (a lane value of 0) gives:
//! * `each op k` when `0 op k == 0` (`*`, `/`, `%`, shifts, `&`; `k op each` when `k op 0 ==
//!   0`; deciders `each cmp k → 1` when `0 cmp k` is false).
//! * Otherwise, or with a different constant per lane: `each(red) op each(green)` with the
//!   constants on a constant combinator (green). The game iterates the union of both wires, so a
//!   lane value of 0 still gives `0 op k` (`+ k`, `^ k`, `| k`, mixed shifts and products).
//!   That costs a constant combinator, so it needs three lanes.
//!
//! This only plans; codegen `logic()` decides which nodes may be lanes (results on the bus
//! under their own signal, not folded into sums, staged, written into bundles, …) and which
//! inputs can be redirected, then emits the packs. Pipelined (`every tick`) blocks have their
//! own emitter and are not vectorised: their values are delayed per depth, and a pack's lanes
//! needn't share one.

use std::collections::{HashMap, HashSet};

use ticky_factorio::{ArOp, CmpOp};

use crate::ir::{Graph, Op, V};

/// What a pack computes per lane.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum PackOp {
    /// `x op k` (`left`: `k op x`).
    Ar { op: ArOp, left: bool },
    /// `x cmp k`, 1 or 0.
    Cmp(CmpOp),
}

/// One scalar operation done by a pack: the node, its non-constant operand, the constant.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Lane {
    pub out: V,
    pub input: V,
    pub k: i32,
}

#[derive(Clone, PartialEq, Eq, Debug)]
pub struct Pack {
    pub op: PackOp,
    pub lanes: Vec<Lane>,
    /// Constants per lane on a constant combinator (`each op each`); else `each op k` with
    /// the lanes' shared `k`.
    pub table: bool,
}

/// Fewest lanes worth a pack: it replaces `n` combinators with one (plus a constant
/// combinator for a table).
const MIN_LANES: usize = 2;
const MIN_TABLE_LANES: usize = 3;

/// `TICKY_NO_SLP=1` turns the pass off (for comparisons).
pub fn enabled() -> bool {
    std::env::var_os("TICKY_NO_SLP").is_none()
}

/// The lane shape of `v`, if it is one: its operation, input and constant.
fn lane_of(g: &Graph, v: V) -> Option<(PackOp, Lane)> {
    let lane = |input, k| Lane { out: v, input, k };
    match *g.op(v) {
        Op::Ar(op, a, b) => match (g.as_const(a), g.as_const(b)) {
            // `x - k` is `x + -k` (wrapping, so k = INT_MIN too): one family with the sums.
            (None, Some(k)) if op == ArOp::Sub => Some((PackOp::Ar { op: ArOp::Add, left: false }, lane(a, k.wrapping_neg()))),
            (None, Some(k)) => Some((PackOp::Ar { op, left: false }, lane(a, k))),
            (Some(k), None) => Some((PackOp::Ar { op, left: true }, lane(b, k))),
            _ => None,
        },
        Op::Cmp(op, a, b) => g.as_const(b).filter(|_| g.as_const(a).is_none()).map(|k| (PackOp::Cmp(op), lane(a, k))),
        _ => None,
    }
}

/// Whether a lane value of 0 (a missing signal, skipped by `each`) gives 0, so `each op k`
/// needs no constants.
fn zero_safe(op: PackOp, k: i32) -> bool {
    match op {
        PackOp::Ar { op, left: false } => op.apply(0, k) == 0,
        PackOp::Ar { op, left: true } => op.apply(k, 0) == 0,
        PackOp::Cmp(op) => !op.apply(0, k),
    }
}

/// Whether a table form is exact for this lane: the constant combinator leaves out a 0, so
/// `0 op 0` (both signals missing) must be 0. Comparisons have no table form.
fn table_ok(op: PackOp, k: i32) -> bool {
    match op {
        PackOp::Ar { op, .. } => k != 0 || op.apply(0, 0) == 0,
        PackOp::Cmp(_) => false,
    }
}

/// Packs among `producers` (in order). `lane_ok(v)`: `v`'s combinator may be replaced by a
/// pack writing its signal where `v`'s value goes. `input_free(x)`: `x` is read only by its lane
/// and its combinators can write the lane's signal onto the pack's wire instead. `place(v)`:
/// the wire `v`'s value is on (a pack writes one; `None` for the bus).
pub fn plan(g: &Graph, producers: &[V], lane_ok: &dyn Fn(V) -> bool, input_free: &dyn Fn(V) -> bool, place: &dyn Fn(V) -> Option<usize>) -> Vec<Pack> {
    type Key = (PackOp, Option<usize>);
    let mut by_k: HashMap<(Key, i32), Vec<Lane>> = HashMap::new();
    let mut order: Vec<(Key, i32)> = Vec::new();
    for &v in producers {
        if !lane_ok(v) {
            continue;
        }
        let Some((op, lane)) = lane_of(g, v) else { continue };
        if !input_free(lane.input) {
            continue;
        }
        let key = ((op, place(v)), lane.k);
        let e = by_k.entry(key).or_default();
        if e.is_empty() {
            order.push(key);
        }
        e.push(lane);
    }
    // Shared constants first; what's left of each operation (one lane per constant, or an
    // unsafe constant) shares a table.
    let mut cands: Vec<Pack> = Vec::new();
    let mut rest: HashMap<Key, Vec<Lane>> = HashMap::new();
    let mut rest_order: Vec<Key> = Vec::new();
    for key in &order {
        let lanes = by_k.remove(key).unwrap();
        let ((op, _), k) = *key;
        if lanes.len() >= MIN_LANES && zero_safe(op, k) {
            cands.push(Pack { op, lanes, table: false });
        } else if table_ok(op, k) {
            let e = rest.entry(key.0).or_default();
            if e.is_empty() {
                rest_order.push(key.0);
            }
            e.extend(lanes);
        }
    }
    for key in rest_order {
        let lanes = rest.remove(&key).unwrap();
        cands.push(Pack { op: key.0, lanes, table: true });
    }
    // Most combinators saved first. A node can't be both a lane (its result where its value
    // goes) and a lane's redirected input, in another pack or the same one (`(x << 3) << 3`).
    cands.sort_by_key(|p| std::cmp::Reverse(p.lanes.len() - usize::from(p.table)));
    let (mut outs, mut ins): (HashSet<V>, HashSet<V>) = Default::default();
    let mut packs = Vec::new();
    for mut p in cands {
        let (mut o, mut i) = (outs.clone(), ins.clone());
        p.lanes.retain(|l| {
            let ok = !i.contains(&l.out) && !o.contains(&l.input);
            if ok {
                o.insert(l.out);
                i.insert(l.input);
            }
            ok
        });
        let min = if p.table { MIN_TABLE_LANES } else { MIN_LANES };
        if p.lanes.len() < min {
            continue;
        }
        p.lanes.sort_by_key(|l| l.out);
        (outs, ins) = (o, i);
        packs.push(p);
    }
    packs
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ir::Iv;

    /// Four lane inputs: `s_i ^ s_(i+1)` over four sources.
    fn graph() -> (Graph, Vec<V>) {
        let mut g = Graph::new(vec![Iv::FULL; 4]);
        let srcs: Vec<V> = (0..4).map(|i| g.src(i)).collect();
        let xs = (0..4).map(|i| g.ar(ArOp::Xor, srcs[i], srcs[(i + 1) % 4])).collect();
        (g, xs)
    }

    #[test]
    fn shared_constant_packs_without_a_table() {
        let (mut g, xs) = graph();
        let k = g.konst(3);
        let ys: Vec<V> = xs.iter().map(|&x| g.ar(ArOp::Mul, x, k)).collect();
        let prods: Vec<V> = xs.iter().chain(&ys).copied().collect();
        let packs = plan(&g, &prods, &|v| ys.contains(&v), &|x| xs.contains(&x), &|_| None);
        assert_eq!(packs.len(), 1);
        assert!(!packs[0].table);
        assert_eq!(packs[0].op, PackOp::Ar { op: ArOp::Mul, left: false });
        assert_eq!(packs[0].lanes.iter().map(|l| (l.out, l.input, l.k)).collect::<Vec<_>>(), (0..4).map(|i| (ys[i], xs[i], 3)).collect::<Vec<_>>());
    }

    #[test]
    fn nonzero_at_zero_needs_a_table_and_three_lanes() {
        let (mut g, xs) = graph();
        let one = g.konst(1);
        // `x + 1` turns a missing signal into 1: table form, so at least three lanes.
        let ys: Vec<V> = xs.iter().map(|&x| g.ar(ArOp::Add, x, one)).collect();
        let prods: Vec<V> = xs.iter().chain(&ys).copied().collect();
        let packs = plan(&g, &prods, &|v| ys[..2].contains(&v), &|x| xs.contains(&x), &|_| None);
        assert!(packs.is_empty());
        let packs = plan(&g, &prods, &|v| ys.contains(&v), &|x| xs.contains(&x), &|_| None);
        assert_eq!(packs.len(), 1);
        assert!(packs[0].table);
    }

    #[test]
    fn mixed_constants_share_a_table() {
        let (mut g, xs) = graph();
        let ys: Vec<V> = xs.iter().enumerate().map(|(i, &x)| {
            let k = g.konst(i as i32 + 1);
            g.ar(ArOp::Shl, x, k)
        }).collect();
        let prods: Vec<V> = xs.iter().chain(&ys).copied().collect();
        let packs = plan(&g, &prods, &|v| ys.contains(&v), &|x| xs.contains(&x), &|_| None);
        assert_eq!(packs.len(), 1);
        assert!(packs[0].table);
        assert_eq!(packs[0].lanes.iter().map(|l| l.k).collect::<Vec<_>>(), vec![1, 2, 3, 4]);
    }

    #[test]
    fn comparisons_only_when_false_at_zero() {
        let (mut g, xs) = graph();
        let (five, neg) = (g.konst(5), g.konst(-5));
        let gt: Vec<V> = xs[..2].iter().map(|&x| g.cmp(CmpOp::Gt, x, five)).collect();
        let lt: Vec<V> = xs[2..].iter().map(|&x| g.cmp(CmpOp::Gt, x, neg)).collect();
        let prods: Vec<V> = xs.iter().chain(&gt).chain(&lt).copied().collect();
        let packs = plan(&g, &prods, &|v| gt.contains(&v) || lt.contains(&v), &|x| xs.contains(&x), &|_| None);
        // `0 > -5` holds, so those two would need a constant: not packed.
        assert_eq!(packs.len(), 1);
        assert_eq!(packs[0].op, PackOp::Cmp(CmpOp::Gt));
        assert_eq!(packs[0].lanes.iter().map(|l| l.out).collect::<Vec<_>>(), gt);
    }

    #[test]
    fn a_lane_is_never_another_lanes_input() {
        let (mut g, xs) = graph();
        let (k, mask) = (g.konst(3), g.konst(255));
        let ys: Vec<V> = xs.iter().map(|&x| g.ar(ArOp::Mul, x, k)).collect();
        let zs: Vec<V> = ys.iter().map(|&y| g.ar(ArOp::And, y, mask)).collect();
        let prods: Vec<V> = xs.iter().chain(&ys).chain(&zs).copied().collect();
        let all: Vec<V> = ys.iter().chain(&zs).copied().collect();
        let packs = plan(&g, &prods, &|v| all.contains(&v), &|x| xs.contains(&x) || ys.contains(&x), &|_| None);
        let outs: HashSet<V> = packs.iter().flat_map(|p| p.lanes.iter().map(|l| l.out)).collect();
        let ins: HashSet<V> = packs.iter().flat_map(|p| p.lanes.iter().map(|l| l.input)).collect();
        assert!(outs.is_disjoint(&ins));
        assert_eq!(outs.len(), 4);
    }

    #[test]
    fn a_lane_is_never_an_input_of_its_own_pack() {
        // `(x << 3) << 3`: both shifts are lanes of one family, but the inner one's result
        // would have to be on the pack's input wire and where its value goes at once.
        let (mut g, xs) = graph();
        let three = g.konst(3);
        let inner: Vec<V> = xs.iter().map(|&x| g.ar(ArOp::Shl, x, three)).collect();
        let outer: Vec<V> = inner.iter().map(|&y| g.ar(ArOp::Shl, y, three)).collect();
        let prods: Vec<V> = xs.iter().chain(&inner).chain(&outer).copied().collect();
        let packs = plan(&g, &prods, &|v| inner.contains(&v) || outer.contains(&v), &|x| xs.contains(&x) || inner.contains(&x), &|_| None);
        assert_eq!(packs.len(), 1);
        assert_eq!(packs[0].lanes.iter().map(|l| l.out).collect::<Vec<_>>(), inner);
    }

    #[test]
    fn subtraction_joins_the_sums_and_places_split_packs() {
        let (mut g, xs) = graph();
        let (five, seven) = (g.konst(5), g.konst(7));
        let ys = vec![g.ar(ArOp::Add, xs[0], five), g.ar(ArOp::Sub, xs[1], seven), g.ar(ArOp::Add, xs[2], seven), g.ar(ArOp::Sub, xs[3], five)];
        let prods: Vec<V> = xs.iter().chain(&ys).copied().collect();
        let packs = plan(&g, &prods, &|v| ys.contains(&v), &|x| xs.contains(&x), &|_| None);
        assert_eq!(packs.len(), 1);
        assert_eq!(packs[0].op, PackOp::Ar { op: ArOp::Add, left: false });
        assert_eq!(packs[0].lanes.iter().map(|l| l.k).collect::<Vec<_>>(), vec![5, -7, 7, -5]);
        // Lanes on two different wires: two lanes each, too few for a table.
        let packs = plan(&g, &prods, &|v| ys.contains(&v), &|x| xs.contains(&x), &|v| Some((v % 2) as usize));
        assert!(packs.is_empty());
    }
}
