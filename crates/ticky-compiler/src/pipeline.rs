//! One-tick pipelining for `every tick:` blocks.
//!
//! A block can run every tick when no state feeds back into itself through a combinator:
//! each state's next value must be ready on the same tick its old value is (it is the old
//! value, a constant, or depends on own state only through conditions that the load
//! deciders check themselves). Everything computed from inputs then flows through the
//! combinators continuously, `latency` ticks behind, with short delay chains so that every
//! combinator sees operands from the same iteration.
//!
//! Accumulators (`x += w`, optionally under a condition, where `w` doesn't depend on the
//! block's own state) also run every tick: `w` is summed straight into the register's
//! feedback wire.
//!
//! Time offsets (τ) are relative to the iteration a value belongs to: own state is at 0
//! (the register output during that iteration's tick), inputs are read at -latency.

use std::collections::{HashMap, HashSet};

use ticky_factorio::ArOp;

use crate::fuse::{is_true, LoadVal, WriterPlan};
use crate::ir::{dnf_operands, Dnf, Graph, Iv, Op, V};
use crate::program::SrcKind;

pub struct Pipe {
    /// Ticks between reading the inputs and the iteration that uses them.
    pub latency: u32,
    /// Candidate schedules (as late as possible, then as soon as possible, if different): the
    /// time offset of each node (by node index), `None` for constants and unused nodes.
    /// Codegen builds the block with each and keeps the smaller.
    pub taus: Vec<Vec<Option<i32>>>,
    /// Registers updated as accumulators.
    pub accs: Vec<(usize, Acc)>,
    /// Sums on the wire ([`wire_sums`]): operands that write a sum's signal, with the sum and
    /// their factor, and the sums (and `* k`) built that way, which have no combinator.
    pub fold: HashMap<V, (V, i32)>,
    pub transparent: HashSet<V>,
}

/// Depth through own-state paths only; `None` for values that don't depend on own state.
fn own_depths(g: &Graph, srcs: &[SrcKind]) -> Vec<Option<i32>> {
    let mut d: Vec<Option<i32>> = vec![None; g.nodes.len()];
    for v in 0..g.nodes.len() as V {
        d[v as usize] = match *g.op(v) {
            Op::Src(s) => matches!(srcs[s as usize], SrcKind::Own(_)).then_some(0),
            Op::Const(_) => None,
            _ => g.operands(v).iter().filter_map(|o| d[*o as usize]).max().map(|m| m + 1),
        };
    }
    d
}

/// Depth from the block's inputs (for values that don't depend on own state). A sum on the
/// wire adds no depth.
fn input_depths(g: &Graph, transparent: &HashSet<V>) -> Vec<i32> {
    let mut d = vec![0i32; g.nodes.len()];
    for v in 0..g.nodes.len() as V {
        let ops = g.operands(v);
        if !ops.is_empty() {
            let lag = if transparent.contains(&v) { 0 } else { 1 };
            d[v as usize] = lag + ops.iter().map(|o| d[*o as usize]).max().unwrap();
        }
    }
    d
}

/// Sums on the wire: combinators writing the same signal onto the bus are added for free,
/// so `a + b` (and `a - b` when `b` can negate itself, and `x * k` when `x` can scale
/// itself) needs no adder when `a` and `b` are only used there and computed on the same
/// tick: they write the sum's signal directly, times a factor. Only for values that don't
/// depend on the block's own state (those are scheduled freely; the parts of a sum are put
/// on the same tick). Returns each part's sum and factor, and the sums.
fn wire_sums(g: &Graph, live: &[V], roots: &[V], od: &[Option<i32>]) -> (HashMap<V, (V, i32)>, HashSet<V>) {
    let mut uses: HashMap<V, usize> = HashMap::new();
    for &v in live {
        for u in g.operands(v) {
            *uses.entry(u).or_default() += 1;
        }
    }
    let sums = Sums { g, uses, roots, od };
    let mut fold: HashMap<V, (V, i64)> = HashMap::new();
    let mut transparent = HashSet::new();
    let absorb = |fold: &mut HashMap<V, (V, i64)>, x: V, t: V, m: i64| {
        fold.insert(x, (t, m));
        // A select's signal arms take the factor from their conditions.
        if m != 1 {
            for c in sums.signal_arm_conds(x) {
                fold.insert(c, (c, m));
            }
        }
    };
    // Users first, so that a sum inside a sum writes the outer one.
    for &v in live.iter().rev() {
        if !sums.free(v) {
            continue;
        }
        let (t, m) = fold.get(&v).copied().unwrap_or((v, 1));
        match *g.op(v) {
            Op::Ar(op @ (ArOp::Add | ArOp::Sub), a, b) if a != b => {
                let mb = if op == ArOp::Sub { -m } else { m };
                if sums.part(a, m) && sums.part(b, mb) {
                    transparent.insert(v);
                    absorb(&mut fold, a, t, m);
                    absorb(&mut fold, b, t, mb);
                }
            }
            // `x * k` with `x` a sum or something that can take the factor itself.
            Op::Ar(ArOp::Mul, a, b) => {
                let (x, k) = match (g.as_const(a), g.as_const(b)) {
                    (None, Some(k)) => (a, k),
                    (Some(k), None) => (b, k),
                    _ => continue,
                };
                let mk = m * k as i64;
                let pushable = matches!(g.op(x), Op::Cmp(..) | Op::Dec(_) | Op::Mux { .. } | Op::Sel(_) | Op::Ar(ArOp::Add | ArOp::Sub, ..) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_));
                if pushable && fits(mk) && sums.part(x, mk) {
                    transparent.insert(v);
                    absorb(&mut fold, x, t, mk);
                }
            }
            _ => {}
        }
    }
    (fold.into_iter().map(|(v, (t, m))| (v, (t, m as i32))).collect(), transparent)
}

fn fits(k: i64) -> bool {
    k > i32::MIN as i64 && k <= i32::MAX as i64
}

/// What [`wire_sums`] may fold.
struct Sums<'a> {
    g: &'a Graph,
    uses: HashMap<V, usize>,
    roots: &'a [V],
    od: &'a [Option<i32>],
}

impl Sums<'_> {
    fn free(&self, v: V) -> bool {
        self.od[v as usize].is_none()
    }

    /// Used once, by another node of the block, and scheduled freely.
    fn single(&self, v: V) -> bool {
        self.uses.get(&v) == Some(&1) && !self.roots.contains(&v) && self.free(v)
    }

    /// The arms of a select (condition, value).
    fn arms(&self, v: V) -> Option<Vec<(V, V)>> {
        match self.g.op(v) {
            Op::Mux { t, f, a, b } => Some(vec![(*t, *a), (*f, *b)]),
            Op::Sel(arms) => Some(arms.clone()),
            _ => None,
        }
    }

    /// The conditions of a select's arms whose values are signals (`x * c`).
    fn signal_arm_conds(&self, v: V) -> Vec<V> {
        self.arms(v).unwrap_or_default().into_iter().filter(|(_, x)| self.g.as_const(*x).is_none()).map(|(c, _)| c).collect()
    }

    /// Whether `o` can write a sum's signal times `m` itself.
    fn part(&self, o: V, m: i64) -> bool {
        let g = self.g;
        let konst = |x: V| g.as_const(x);
        if !self.single(o) {
            return false;
        }
        match *g.op(o) {
            Op::BGet(..) | Op::BTotal(_) | Op::BCount(_) | Op::Cmp(..) => fits(m),
            Op::Dec(ref arms) => arms.iter().all(|(_, k)| fits(*k as i64 * m)),
            Op::Ar(..) | Op::Mux { .. } | Op::Sel(_) if m == 1 => true,
            // Constant arms scale; signal arms `x * c` scale through `c` when only they use it.
            Op::Mux { .. } | Op::Sel(_) => self.arms(o).unwrap().iter().all(|&(c, x)| match konst(x) {
                Some(k) => fits(k as i64 * m),
                None => self.single(c) && self.part(c, m) && matches!(g.op(c), Op::Cmp(..) | Op::Dec(_)),
            }),
            Op::Ar(ArOp::Sub, ..) if m == -1 => true,
            Op::Ar(ArOp::Mul, x, y) => konst(x).or(konst(y)).is_some_and(|k| fits(k as i64 * m)),
            Op::Ar(ArOp::Div, _, y) if m == -1 => konst(y).is_some_and(|k| k != i32::MIN && k != 0),
            Op::Ar(op @ (ArOp::Add | ArOp::Sub), x, y) => x != y && self.part(x, m) && self.part(y, if op == ArOp::Sub { -m } else { m }),
            _ => false,
        }
    }
}

/// A register updated every tick as `x += w`, except when one of `consts` applies.
#[derive(Clone, Debug)]
pub struct Acc {
    /// The increment (already zero whenever the plan says "keep").
    pub w: V,
    /// Constant loads that override the increment: `(condition, value)`.
    pub consts: Vec<(Dnf, i32)>,
    /// When none of `consts` applies (the accumulator adds `w`).
    pub otherwise: Dnf,
}

/// The accumulator form of a plan, if it is one: `x = x + w` (or `x - w`), possibly under a
/// condition and alongside constant loads (e.g. a reset), with `w` and that condition
/// independent of the block's own state.
fn accumulator(g: &mut Graph, plan: &WriterPlan, own: V, od: &[Option<i32>]) -> Option<Acc> {
    let free = |x: V| od[x as usize].is_none();
    let mut add: Option<(Dnf, V)> = None;
    let mut consts = Vec::new();
    for l in &plan.loads {
        match l.val {
            LoadVal::Const(k) => consts.push((l.guard.clone(), k)),
            LoadVal::Node(v) if add.is_none() => {
                let w = match *g.op(v) {
                    Op::Ar(ArOp::Add, a, b) if a == own && free(b) => b,
                    Op::Ar(ArOp::Add, a, b) if b == own && free(a) => a,
                    Op::Ar(ArOp::Sub, a, b) if a == own && free(b) => {
                        let z = g.konst(0);
                        g.ar(ArOp::Sub, z, b)
                    }
                    _ => return None,
                };
                add = Some((l.guard.clone(), w));
            }
            LoadVal::Node(_) => return None,
        }
    }
    let (guard, w) = add?;
    let mut otherwise: Dnf = vec![vec![]];
    for (d, _) in &consts {
        otherwise = crate::fuse::and_dnf(&otherwise, &crate::fuse::negate(d)?)?;
    }
    let w = if is_true(&guard) {
        w
    } else {
        if !dnf_operands(&guard).all(free) {
            return None;
        }
        // Add nothing when the condition is false.
        let c = g.dec(vec![(guard, 1)], Iv::BOOL);
        let z = g.konst(0);
        g.mux(c, w, z)
    };
    Some(Acc { w, consts, otherwise })
}

/// Plans one-tick pipelining for a block, or `None` if a state feeds back through logic.
/// On success, accumulator registers are removed from `plans` (they're in `Pipe::accs`).
pub fn plan(g: &mut Graph, srcs: &[SrcKind], plans: &mut Vec<(usize, WriterPlan)>) -> Option<Pipe> {
    let od = own_depths(g, srcs);
    let own_node = |g: &mut Graph, si: usize| {
        srcs.iter().position(|k| *k == SrcKind::Own(si)).map(|id| g.src(id as u32))
    };

    // Accumulators first; everything else must be ready at offset 0.
    let mut accs = Vec::new();
    let mut rest = Vec::new();
    for (si, p) in plans.iter() {
        if let Some(own) = own_node(g, *si) {
            if let Some(w) = accumulator(g, p, own, &od) {
                accs.push((*si, w));
                continue;
            }
        }
        rest.push((*si, p.clone()));
    }
    let od = own_depths(g, srcs); // accumulator() may have added nodes
    for (_, a) in &accs {
        // Constant loads are checked on the commit tick, like direct loads.
        let conds = a.consts.iter().flat_map(|(d, _)| dnf_operands(d)).chain(dnf_operands(&a.otherwise));
        if !conds.into_iter().all(|v| od[v as usize].is_none_or(|d| d <= 0)) {
            return None;
        }
    }
    let at_most = |nodes: &mut dyn Iterator<Item = V>, limit: i32| {
        let mut ok = true;
        for v in nodes {
            ok &= od[v as usize].is_none_or(|d| d <= limit);
        }
        ok
    };
    for (_, p) in &rest {
        for l in &p.loads {
            let ok = match (&l.val, l.direct, is_true(&l.guard)) {
                (_, true, _) => at_most(&mut dnf_operands(&l.guard), 0),
                (LoadVal::Node(v), _, true) => at_most(&mut [*v].into_iter(), 0),
                (LoadVal::Const(_), _, true) => true,
                (LoadVal::Node(v), false, false) => {
                    at_most(&mut [*v].into_iter(), 0) && at_most(&mut dnf_operands(&l.guard), -1)
                }
                (LoadVal::Const(_), false, false) => at_most(&mut dnf_operands(&l.guard), -1),
            };
            if !ok {
                return None;
            }
        }
        if let Some(k) = &p.keep {
            if !at_most(&mut dnf_operands(k), 0) {
                return None;
            }
        }
    }

    // Each use of an input-derived value fixes a lower bound on the input latency.
    let mut need: Vec<(V, i32)> = Vec::new(); // (value, offset it's needed at)
    for (_, p) in &rest {
        for l in &p.loads {
            let guard_at = if l.direct || is_true(&l.guard) { 0 } else { -1 };
            need.extend(dnf_operands(&l.guard).map(|v| (v, guard_at)));
            if let LoadVal::Node(v) = l.val {
                need.push((v, 0));
            }
        }
        if let Some(k) = &p.keep {
            need.extend(dnf_operands(k).map(|v| (v, 0)));
        }
    }
    for (_, a) in &accs {
        need.push((a.w, -1));
        need.extend(a.consts.iter().flat_map(|(d, _)| dnf_operands(d)).map(|v| (v, 0)));
        need.extend(dnf_operands(&a.otherwise).map(|v| (v, 0)));
    }
    let roots: Vec<V> = need.iter().map(|(v, _)| *v).collect();
    let live = g.reachable(&roots);
    let (fold, transparent) = wire_sums(g, &live, &roots, &od);
    // How much later than its operand `u` a node `w` is: 0 for a sum on the wire.
    let lag = |w: V| if transparent.contains(&w) { 0 } else { 1 };
    let din = input_depths(g, &transparent);
    let mut latency = 0i32;
    let free = |v: V| od[v as usize].is_none() && g.as_const(v).is_none();
    for &(v, at) in &need {
        if free(v) {
            latency = latency.max(din[v as usize] - at);
        }
    }
    for &v in &live {
        if let Some(t) = od[v as usize] {
            for u in g.operands(v) {
                if free(u) {
                    latency = latency.max(din[u as usize] - (t - 1));
                }
            }
        }
    }

    let mut tau: Vec<Option<i32>> = vec![None; g.nodes.len()];
    for &v in &live {
        tau[v as usize] = match *g.op(v) {
            Op::Const(_) => None,
            Op::Src(s) if matches!(srcs[s as usize], SrcKind::Own(_)) => Some(0),
            Op::Src(_) => Some(-latency),
            _ => g.operands(v).iter().filter_map(|o| tau[*o as usize]).max().map(|m| m + lag(v)),
        };
    }
    // Then as late as possible: values that only depend on inputs are computed just before
    // they're needed, so values are delayed close to the inputs, where many consumers
    // share one delay chain, rather than once per result.
    let mut users: Vec<Vec<V>> = vec![Vec::new(); g.nodes.len()];
    for &v in &live {
        for u in g.operands(v) {
            users[u as usize].push(v);
        }
    }
    let mut latest: Vec<Option<i32>> = vec![None; g.nodes.len()];
    for &(v, at) in &need {
        let l = &mut latest[v as usize];
        *l = Some(l.map_or(at, |x| x.min(at)));
    }
    // Nodes computed from constants alone (a random pick from a constant table) aren't
    // timed by their operands: they run just before their first use.
    for &v in live.iter().rev() {
        if tau[v as usize].is_some() || matches!(g.op(v), Op::Const(_) | Op::BConst(_)) || g.operands(v).is_empty() {
            continue;
        }
        let mut t = latest[v as usize];
        for &w in &users[v as usize] {
            if let Some(tw) = tau[w as usize] {
                t = Some(t.map_or(tw - lag(w), |x| x.min(tw - lag(w))));
            }
        }
        tau[v as usize] = Some(t.unwrap_or(1));
    }
    // The parts of a sum on the wire all write it on the same tick.
    let mut asap = tau.clone();
    for &v in live.iter().rev() {
        if transparent.contains(&v) {
            for u in g.operands(v) {
                if asap[u as usize].is_some() && g.as_const(u).is_none() {
                    asap[u as usize] = asap[v as usize];
                }
            }
        }
    }
    for &v in live.iter().rev() {
        let movable = od[v as usize].is_none() && !matches!(g.op(v), Op::Const(_) | Op::Src(_) | Op::BConst(_));
        if !movable {
            continue;
        }
        let mut t = latest[v as usize];
        for &w in &users[v as usize] {
            if let Some(tw) = tau[w as usize] {
                t = Some(t.map_or(tw - lag(w), |x| x.min(tw - lag(w))));
            }
        }
        if let (Some(t), Some(cur)) = (t, tau[v as usize]) {
            if t > cur {
                tau[v as usize] = Some(t);
            }
        }
    }
    // Neither schedule always wins (late is worse when a result has many consumers).
    let mut taus = vec![tau];
    if asap != taus[0] {
        taus.push(asap);
    }
    *plans = rest;
    Some(Pipe { latency: latency as u32, taus, accs, fold, transparent })
}
