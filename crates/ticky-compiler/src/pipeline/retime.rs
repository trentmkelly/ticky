//! Retiming of pipelined blocks: which schedules (node time offsets τ) are legal, and the
//! one needing the fewest delays.
//!
//! A pipelined block's schedule is a retiming in Leiserson–Saxe's sense: inputs are read at
//! `-latency`, own state and the loads are at fixed offsets, and every other node may sit
//! anywhere between its operands (one tick later than the latest, the same tick for a sum on
//! the wire) and its first use. Moving a node moves the delays across it: values delayed
//! before it become delayed after it and vice versa. Every legal schedule computes the same
//! values on the same ticks (the outputs are read at fixed offsets), so the choice only
//! changes how many delay combinators the block needs.
//!
//! [`Space::min_delays`] minimises the delays as a linear program over the τ (Leiserson and
//! Saxe's minimum-register retiming, with fanout sharing: a value's readers share one delay
//! chain, so it costs its last read minus when it's computed). The constraints are
//! differences of two variables, so the dual is a min-cost flow and the optimum is integral.
//! The pipeliner adds the result to its candidate schedules; codegen's trial builds keep
//! whichever is smallest, so a retimed schedule is only used where it saves combinators.

use std::collections::HashSet;

use crate::ir::{Graph, Op, V};

/// The legal schedules of one block.
#[derive(Clone, Debug, Default)]
pub struct Space {
    /// Groups of nodes that move together (a sum on the wire and its parts share a tick).
    pub groups: Vec<Vec<V>>,
    /// The latest tick each node can be computed on: the first offset a load (or an
    /// accumulator, or a combinational output) reads it at. None: read only by other nodes.
    pub latest: Vec<Option<i32>>,
    /// The last offset a load reads each node at (its delay runs at least that far).
    pub last: Vec<Option<i32>>,
}

/// Whether `v` may be moved: computed by a combinator of the block from values that don't
/// depend on own state, and not a random pick (whose stream follows its tick).
pub(super) fn movable_op(g: &Graph, v: V) -> bool {
    matches!(
        g.op(v),
        Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) | Op::Sel(_) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_) | Op::AGet(..) | Op::BDot(..)
            | Op::Bun(_) | Op::BMux { .. } | Op::BDec(_) | Op::BSelect(..) | Op::BSelectAt(..)
    )
}

impl Space {
    pub(super) fn new(g: &Graph, live: &[V], movable: &dyn Fn(V) -> bool, transparent: &HashSet<V>, latest: Vec<Option<i32>>, last: Vec<Option<i32>>) -> Space {
        // Union-find over "same tick" edges: a transparent node and its non-constant operands.
        let n = g.nodes.len();
        let mut parent: Vec<usize> = (0..n).collect();
        fn find(p: &mut [usize], x: usize) -> usize {
            let mut r = x;
            while p[r] != r {
                r = p[r];
            }
            let mut y = x;
            while p[y] != r {
                let next = p[y];
                p[y] = r;
                y = next;
            }
            r
        }
        let mut fixed: HashSet<usize> = HashSet::new();
        for &v in live {
            if !movable(v) {
                fixed.insert(v as usize);
            }
            if transparent.contains(&v) {
                for u in g.operands(v) {
                    if g.as_const(u).is_none() {
                        let (a, b) = (find(&mut parent, u as usize), find(&mut parent, v as usize));
                        parent[a] = b;
                    }
                }
            }
        }
        let fixed_roots: HashSet<usize> = fixed.iter().map(|&v| find(&mut parent, v)).collect();
        let mut groups: std::collections::BTreeMap<usize, Vec<V>> = Default::default();
        for &v in live {
            let r = find(&mut parent, v as usize);
            if !fixed_roots.contains(&r) && movable(v) {
                groups.entry(r).or_default().push(v);
            }
        }
        Space { groups: groups.into_values().collect(), latest, last }
    }

    /// Whether every node of `tau` is between its operands and its uses.
    pub fn legal(&self, g: &Graph, transparent: &HashSet<V>, tau: &[Option<i32>]) -> bool {
        for v in 0..tau.len() as V {
            let Some(t) = tau[v as usize] else { continue };
            if self.latest[v as usize].is_some_and(|l| t > l) {
                return false;
            }
            if matches!(g.op(v), Op::Src(_)) {
                continue;
            }
            for u in g.operands(v) {
                let Some(tu) = tau[u as usize] else { continue };
                if g.as_const(u).is_some() {
                    continue;
                }
                let ok = if transparent.contains(&v) { tu == t } else { tu < t };
                if !ok {
                    return false;
                }
            }
        }
        true
    }

    /// The schedule needing the fewest delays by `w` (Leiserson–Saxe with fanout sharing):
    /// for each value, the ticks between it being computed and its last read count once
    /// (its readers share one delay chain), times its weight. Values written onto a sum's
    /// signal (`part`) aren't counted. Of the optimal schedules, the latest.
    pub fn min_delays(&self, g: &Graph, transparent: &HashSet<V>, part: &dyn Fn(V) -> bool, tau: &[Option<i32>], w: Weights) -> Option<Vec<Option<i32>>> {
        let n = tau.len();
        let mut cs = Constraints { vars: 1, arcs: Vec::new(), supply: vec![0] };
        // Each node as (variable, offset): movable groups get a variable, the rest are fixed.
        let mut at: Vec<(usize, i64)> = (0..n).map(|v| (0, tau[v].unwrap_or(0) as i64)).collect();
        for gr in &self.groups {
            let x = cs.var();
            for &v in gr {
                at[v as usize] = (x, 0);
            }
        }
        let big = 2 + self.latest.iter().chain(&self.last).flatten().copied().max().unwrap_or(0).max(0) as i64;
        let mut ok = true;
        for x in 1..cs.vars {
            ok &= cs.le((x, 0), (0, 0), big);
        }
        let mut readers: Vec<Vec<V>> = vec![Vec::new(); n];
        for v in 0..n as V {
            if tau[v as usize].is_none() {
                continue;
            }
            if let Some(l) = self.latest[v as usize] {
                ok &= cs.le(at[v as usize], (0, 0), l as i64);
            }
            if matches!(g.op(v), Op::Src(_)) {
                continue;
            }
            for u in g.operands(v) {
                if tau[u as usize].is_none() || g.as_const(u).is_some() {
                    continue;
                }
                if transparent.contains(&v) {
                    ok &= cs.le(at[u as usize], at[v as usize], 0);
                    ok &= cs.le(at[v as usize], at[u as usize], 0);
                } else {
                    ok &= cs.le(at[u as usize], at[v as usize], -1);
                    readers[u as usize].push(v);
                }
            }
        }
        if !ok {
            return None;
        }
        // The cost: for each value, (its last read - when it's computed) × weight, the last
        // read being a variable `m` above every read.
        for u in 0..n as V {
            if tau[u as usize].is_none() || g.as_const(u).is_some() || matches!(g.op(u), Op::BConst(_)) || part(u) {
                continue;
            }
            let wt = if g.is_bundle(u) { w.bundle } else { w.scalar };
            if wt == 0 || readers[u as usize].is_empty() && self.last[u as usize].is_none() {
                continue;
            }
            let m = cs.var();
            cs.le((m, 0), (0, 0), big);
            for &r in &readers[u as usize] {
                // Read on the tick before the reader's.
                cs.le(at[r as usize], (m, 0), 1);
            }
            if let Some(l) = self.last[u as usize] {
                cs.le((0, l as i64), (m, 0), 0);
            }
            cs.supply[m] += wt;
            let (x, _) = at[u as usize];
            if x != 0 {
                cs.supply[x] -= wt;
            }
        }
        let x = cs.solve()?;
        let mut out = tau.to_vec();
        for v in 0..n {
            if let (Some(_), (var, off)) = (tau[v], at[v]) {
                if var != 0 {
                    out[v] = Some(i32::try_from(x[var] + off).ok()?);
                }
            }
        }
        self.legal(g, transparent, &out).then_some(out)
    }
}

/// What delaying a value costs per tick, by kind: a bundle has its own delay chain (one
/// combinator per tick, shared by its readers); scalars share carry wires with the rest of
/// the block, so they usually cost less.
#[derive(Clone, Copy, Debug)]
pub struct Weights {
    pub bundle: i64,
    pub scalar: i64,
}

/// Shortest distances, and each node's last arc (index, whether forward).
type Paths = (Vec<i64>, Vec<Option<(usize, bool)>>);

/// Difference constraints `x_j - x_i <= b` over integer variables; variable 0 is the
/// reference (at 0). `supply` holds the objective's coefficients.
struct Constraints {
    vars: usize,
    arcs: Vec<(usize, usize, i64)>,
    supply: Vec<i64>,
}

impl Constraints {
    fn var(&mut self) -> usize {
        self.vars += 1;
        self.supply.push(0);
        self.vars - 1
    }

    /// `x_j + oj - (x_i + oi) <= b`. False if it can't hold (both sides fixed).
    fn le(&mut self, (j, oj): (usize, i64), (i, oi): (usize, i64), b: i64) -> bool {
        let b = b + oi - oj;
        if i == j {
            return b >= 0;
        }
        self.arcs.push((i, j, b));
        true
    }

    /// Minimises `sum(supply_k * x_k)` and returns the largest optimal `x` (with `x_0 = 0`),
    /// or `None` if the solver gives up. The dual is a min-cost flow (net outflow `supply_k`
    /// at node k, arc `i → j` of cost `b` per constraint, unbounded capacity), solved by
    /// successive shortest paths; `x` is then the shortest distances from node 0 in the
    /// residual graph (complementary slackness: arcs carrying flow are tight).
    fn solve(mut self) -> Option<Vec<i64>> {
        let n = self.vars;
        let total: i64 = self.supply[1..].iter().sum();
        self.supply[0] = -total;
        let m = self.arcs.len();
        let mut flow = vec![0i64; m];
        let mut out: Vec<Vec<usize>> = vec![Vec::new(); n];
        let mut inn: Vec<Vec<usize>> = vec![Vec::new(); n];
        for (a, &(i, j, _)) in self.arcs.iter().enumerate() {
            out[i].push(a);
            inn[j].push(a);
        }
        let mut excess = self.supply.clone();
        let inf = i64::MAX / 4;
        let arcs = &self.arcs;
        // Shortest paths from `starts` in the residual graph (queue-based Bellman–Ford);
        // `pred` is (arc, forward). `None` on a negative cycle (an infeasible system).
        let paths = |flow: &[i64], starts: &[usize]| -> Option<Paths> {
            let mut dist = vec![inf; n];
            let mut pred: Vec<Option<(usize, bool)>> = vec![None; n];
            let mut queued = vec![false; n];
            let mut pops = vec![0usize; n];
            let mut q = std::collections::VecDeque::new();
            for &s in starts {
                dist[s] = 0;
                queued[s] = true;
                q.push_back(s);
            }
            while let Some(x) = q.pop_front() {
                queued[x] = false;
                pops[x] += 1;
                if pops[x] > n + 1 {
                    return None;
                }
                let dx = dist[x];
                let mut relax = |y: usize, d: i64, p: (usize, bool)| {
                    if d < dist[y] {
                        dist[y] = d;
                        pred[y] = Some(p);
                        if !queued[y] {
                            queued[y] = true;
                            q.push_back(y);
                        }
                    }
                };
                for &a in &out[x] {
                    relax(arcs[a].1, dx + arcs[a].2, (a, true));
                }
                for &a in &inn[x] {
                    if flow[a] > 0 {
                        relax(arcs[a].0, dx - arcs[a].2, (a, false));
                    }
                }
            }
            Some((dist, pred))
        };
        for _ in 0..100_000 {
            let sources: Vec<usize> = (0..n).filter(|&k| excess[k] > 0).collect();
            if sources.is_empty() {
                break;
            }
            let (dist, pred) = paths(&flow, &sources)?;
            let t = (0..n).filter(|&k| excess[k] < 0 && dist[k] < inf).min_by_key(|&k| dist[k])?;
            // Back to the source the path started from, finding the bottleneck.
            let mut push = -excess[t];
            let mut y = t;
            for _ in 0..=n {
                let Some((a, fwd)) = pred[y] else { break };
                if !fwd {
                    push = push.min(flow[a]);
                }
                y = if fwd { arcs[a].0 } else { arcs[a].1 };
            }
            if pred[y].is_some() || excess[y] <= 0 {
                return None;
            }
            let s = y;
            push = push.min(excess[s]);
            let mut y = t;
            while y != s {
                let (a, fwd) = pred[y]?;
                if fwd {
                    flow[a] += push;
                    y = arcs[a].0;
                } else {
                    flow[a] -= push;
                    y = arcs[a].1;
                }
            }
            excess[s] -= push;
            excess[t] += push;
        }
        if excess.iter().any(|&e| e != 0) {
            return None;
        }
        let (dist, _) = paths(&flow, &[0])?;
        dist.iter().all(|&d| d < inf).then_some(dist)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// A small deterministic generator (no rand dependency).
    struct Lcg(u64);

    impl Lcg {
        fn next(&mut self, n: i64) -> i64 {
            self.0 = self.0.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            ((self.0 >> 33) % n as u64) as i64
        }
    }

    #[test]
    fn solver_matches_brute_force() {
        let mut r = Lcg(7);
        let mut solved = 0;
        for _ in 0..400 {
            let vars = 1 + r.next(4) as usize;
            let mut cs = Constraints { vars: 1, arcs: Vec::new(), supply: vec![0] };
            for _ in 0..vars {
                let x = cs.var();
                cs.le((x, 0), (0, 0), 3); // x <= 3
                cs.le((0, 0), (x, 0), 3); // x >= -3
                cs.supply[x] = r.next(7) - 3;
            }
            for _ in 0..r.next(6) {
                let (j, i, b) = (r.next(vars as i64 + 1) as usize, r.next(vars as i64 + 1) as usize, r.next(7) - 3);
                cs.le((j, 0), (i, 0), b);
            }
            let supply = cs.supply.clone();
            let arcs = cs.arcs.clone();
            // Brute force over the box.
            let mut best: Option<i64> = None;
            let mut optima = Vec::new();
            for code in 0..7i64.pow(vars as u32) {
                let mut x = vec![0i64];
                let mut c = code;
                for _ in 0..vars {
                    x.push(c % 7 - 3);
                    c /= 7;
                }
                if arcs.iter().any(|&(i, j, b)| x[j] - x[i] > b) {
                    continue;
                }
                let cost: i64 = (1..=vars).map(|k| supply[k] * x[k]).sum();
                if best.is_none_or(|b| cost < b) {
                    best = Some(cost);
                    optima.clear();
                }
                if best == Some(cost) {
                    optima.push(x);
                }
            }
            match (best, cs.solve()) {
                (None, None) => {}
                (Some(b), Some(x)) => {
                    assert!(arcs.iter().all(|&(i, j, c)| x[j] - x[i] <= c), "infeasible {x:?}");
                    let cost: i64 = (1..=vars).map(|k| supply[k] * x[k]).sum();
                    assert_eq!(cost, b, "not optimal: {x:?} for {supply:?} {arcs:?}");
                    assert!(optima.iter().all(|y| (1..=vars).all(|k| y[k] <= x[k])), "{x:?} isn't the largest optimum");
                    solved += 1;
                }
                (b, x) => panic!("brute force {b:?}, solver {x:?} for {supply:?} {arcs:?}"),
            }
        }
        assert!(solved > 200, "{solved}");
    }
}
