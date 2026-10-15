//! Equality saturation over the scalar IR (PLAN.md §3).
//!
//! ir.rs simplifies while it builds nodes: each rewrite fires when its constructor is called,
//! in a fixed order, and a form no constructor produces right away is never considered. Here,
//! once a unit (an `every` block or a process) is lowered and before fusion, the scalar part
//! of its graph reachable from the unit's roots (arithmetic, comparisons and selects; anything
//! else, comprehension lowering included, is an opaque leaf) goes into an e-graph. Rewrite
//! rules add equivalent forms until nothing new appears or a limit is hit, then the cheapest
//! form of each root is extracted and rebuilt with the ordinary constructors (which simplify
//! further and, with `TICKY_EXPORT_IR`, log their claims).
//!
//! **Intervals.** Every e-class carries an interval: the intersection of its members' (graph
//! nodes keep the interval ir.rs gave them, which select conditions may have narrowed; new
//! nodes get one from their operands). All members are the same value for every input, so
//! the intersection is sound wherever the class is used. Rules that need a fact (a sum that
//! can't wrap, a divisor that can't be 0) test the class intervals, never the path conditions
//! a node was built under: a rewrite is an equality everywhere, never only on some path.
//! A class whose interval pins one value gets that constant as a member.
//!
//! **Cost.** Extraction minimises combinators as `codegen::logic` builds them: constants,
//! sources and leaves are free; `a + b` and `a - b` are free when both operands are
//! combinators writing the sum's signal (wire sums); `x * k` is free when `x` can take the
//! factor itself (a comparison, select or sum); a select costs a decider per arm that isn't
//! 0, and comparisons only used as its conditions are tested by those deciders. Ties go to
//! the smaller expression. A unit's new roots are kept only if the same model, counted over
//! the whole unit with sharing (single-use operands only for wire sums), says strictly fewer
//! combinators and no root got deeper; `lib.rs` also builds the program without the pass and
//! keeps that build unless this one is no larger and no slower.
//!
//! **Limits.** At most [`MAX_ITERS`] rounds of rules, and rules stop adding nodes past
//! [`node_limit`] (a multiple of the unit's size): big units stay fast.
//!
//! `TICKY_EGRAPH=0` turns the pass off; `TICKY_EGRAPH_STATS=1` prints what it did per unit.

use std::cell::Cell;
use std::collections::{HashMap, HashSet};

use ticky_factorio::{ArOp, CmpOp};

use crate::ir::{ar_interval, decide, Graph, Iv, Op, V};
use crate::ir_export::Req;

type Id = u32;

/// Rounds of rule application.
pub const MAX_ITERS: usize = 8;

/// Most e-nodes a unit with `n` scalar nodes may grow to.
pub fn node_limit(n: usize) -> usize {
    (4 * n + 256).min(60_000)
}

/// Units with more scalar nodes than this are left alone (compile time).
const MAX_UNIT: usize = 20_000;

const MIN: i64 = i32::MIN as i64;
const MAX: i64 = i32::MAX as i64;

thread_local! {
    static ENABLED: Cell<bool> = const { Cell::new(true) };
    static CHANGED: Cell<usize> = const { Cell::new(0) };
}

/// Whether the pass runs (off with `TICKY_EGRAPH=0`, or [`set_enabled`]).
pub fn enabled() -> bool {
    ENABLED.with(|c| c.get()) && std::env::var("TICKY_EGRAPH").map_or(true, |v| v != "0")
}

/// Turns the pass on or off for this thread (`lib.rs` builds with and without it).
pub fn set_enabled(on: bool) {
    ENABLED.with(|c| c.set(on));
}

/// How many units the pass changed since [`reset_changed`].
pub fn changed() -> usize {
    CHANGED.with(|c| c.get())
}

pub fn reset_changed() {
    CHANGED.with(|c| c.set(0));
}

fn stats_on() -> bool {
    std::env::var_os("TICKY_EGRAPH_STATS").is_some()
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
enum ENode {
    Const(i32),
    /// A graph node kept as it is: sources, bundle reads, deciders, anything that isn't scalar
    /// arithmetic, a comparison or a select, and every node of comprehension lowering.
    Leaf(V),
    Ar(ArOp, Id, Id),
    Cmp(CmpOp, Id, Id),
    /// `(t ? a : 0) + (f ? b : 0)` with complementary `t`, `f` ([`Op::Mux`]).
    Mux(Id, Id, Id, Id),
}

impl ENode {
    fn children(&self) -> Vec<Id> {
        match *self {
            ENode::Const(_) | ENode::Leaf(_) => vec![],
            ENode::Ar(_, a, b) | ENode::Cmp(_, a, b) => vec![a, b],
            ENode::Mux(t, f, a, b) => vec![t, f, a, b],
        }
    }

    fn map(&self, f: impl Fn(Id) -> Id) -> ENode {
        match *self {
            ENode::Const(_) | ENode::Leaf(_) => *self,
            ENode::Ar(op, a, b) => ENode::Ar(op, f(a), f(b)),
            ENode::Cmp(op, a, b) => ENode::Cmp(op, f(a), f(b)),
            ENode::Mux(t, g, a, b) => ENode::Mux(f(t), f(g), f(a), f(b)),
        }
    }
}

/// A term to add to the e-graph (and union with the class a rule matched).
#[derive(Clone, Debug)]
enum T {
    C(Id),
    K(i32),
    Ar(ArOp, Box<T>, Box<T>),
    Cmp(CmpOp, Box<T>, Box<T>),
    Mux(Id, Id, Box<T>, Box<T>),
}

fn ar(op: ArOp, a: T, b: T) -> T {
    T::Ar(op, Box::new(a), Box::new(b))
}

fn cmp(op: CmpOp, a: T, b: T) -> T {
    T::Cmp(op, Box::new(a), Box::new(b))
}

fn mux(t: Id, f: Id, a: T, b: T) -> T {
    T::Mux(t, f, Box::new(a), Box::new(b))
}

struct Class {
    nodes: Vec<ENode>,
    parents: Vec<(ENode, Id)>,
    iv: Iv,
}

struct EGraph<'g> {
    g: &'g Graph,
    parent: Vec<Id>,
    classes: Vec<Class>,
    memo: HashMap<ENode, Id>,
    /// Classes whose parents need re-canonicalising.
    pending: Vec<Id>,
    /// Classes whose interval narrowed (their parents' may narrow too).
    narrowed: Vec<Id>,
    /// Interval re-analysis steps left (narrowing through cycles could go on for long).
    budget: usize,
    /// Two members with disjoint intervals: some interval was wrong, so nothing is trusted.
    conflict: bool,
}

fn meet(a: Iv, b: Iv) -> Iv {
    Iv { lo: a.lo.max(b.lo), hi: a.hi.min(b.hi) }
}

fn fits(x: i64) -> bool {
    (MIN..=MAX).contains(&x)
}

impl<'g> EGraph<'g> {
    fn new(g: &'g Graph) -> Self {
        EGraph { g, parent: Vec::new(), classes: Vec::new(), memo: HashMap::new(), pending: Vec::new(), narrowed: Vec::new(), budget: 0, conflict: false }
    }

    fn find(&self, mut a: Id) -> Id {
        while self.parent[a as usize] != a {
            a = self.parent[a as usize];
        }
        a
    }

    fn canon(&self, n: &ENode) -> ENode {
        n.map(|c| self.find(c))
    }

    fn iv(&self, a: Id) -> Iv {
        self.classes[self.find(a) as usize].iv
    }

    /// The class's value, if its interval pins it.
    fn k(&self, a: Id) -> Option<i32> {
        let i = self.iv(a);
        (i.lo == i.hi).then_some(i.lo as i32)
    }

    fn is_bool(&self, a: Id) -> bool {
        self.iv(a).is_bool()
    }

    fn nodes(&self, a: Id) -> &[ENode] {
        &self.classes[self.find(a) as usize].nodes
    }

    /// The `op` nodes of class `a`, as (left, right).
    fn ars(&self, a: Id, op: ArOp) -> Vec<(Id, Id)> {
        self.nodes(a).iter().filter_map(|n| match *n {
            ENode::Ar(o, x, y) if o == op => Some((x, y)),
            _ => None,
        }).collect()
    }

    /// `a` as `x op k` (both operand orders for commutative ops): (x, k).
    fn ar_k(&self, a: Id, op: ArOp) -> Vec<(Id, i32)> {
        let mut out = Vec::new();
        for (x, y) in self.ars(a, op) {
            if let Some(k) = self.k(y) {
                out.push((x, k));
            } else if let (true, Some(k)) = (op.commutative(), self.k(x)) {
                out.push((y, k));
            }
        }
        out
    }

    /// The interval of a node from its operands' classes.
    fn node_iv(&self, n: &ENode) -> Iv {
        match *n {
            ENode::Const(k) => Iv::k(k),
            ENode::Leaf(v) => self.g.iv(v),
            ENode::Ar(op, a, b) => ar_interval(op, self.iv(a), self.iv(b), self.k(b)),
            ENode::Cmp(op, a, b) => {
                if self.find(a) == self.find(b) {
                    return Iv::k(matches!(op, CmpOp::Eq | CmpOp::Ge | CmpOp::Le) as i32);
                }
                match decide(op, self.iv(a), self.iv(b)) {
                    Some(d) => Iv::k(d as i32),
                    None => Iv::BOOL,
                }
            }
            ENode::Mux(_, _, a, b) => self.iv(a).join(self.iv(b)),
        }
    }

    fn add(&mut self, n: ENode) -> Id {
        let n = self.canon(&n);
        if let Some(&id) = self.memo.get(&n) {
            return self.find(id);
        }
        let id = self.classes.len() as Id;
        let iv = self.node_iv(&n);
        self.parent.push(id);
        self.classes.push(Class { nodes: vec![n], parents: Vec::new(), iv });
        for c in n.children() {
            let c = self.find(c);
            self.classes[c as usize].parents.push((n, id));
        }
        self.memo.insert(n, id);
        if iv.lo == iv.hi && !matches!(n, ENode::Const(_)) {
            let k = self.add(ENode::Const(iv.lo as i32));
            self.union(id, k);
        }
        id
    }

    fn add_term(&mut self, t: &T) -> Id {
        match t {
            T::C(id) => self.find(*id),
            T::K(k) => self.add(ENode::Const(*k)),
            T::Ar(op, a, b) => {
                let (a, b) = (self.add_term(a), self.add_term(b));
                self.add(ENode::Ar(*op, a, b))
            }
            T::Cmp(op, a, b) => {
                let (a, b) = (self.add_term(a), self.add_term(b));
                self.add(ENode::Cmp(*op, a, b))
            }
            T::Mux(t, f, a, b) => {
                let (a, b) = (self.add_term(a), self.add_term(b));
                self.add(ENode::Mux(*t, *f, a, b))
            }
        }
    }

    /// Narrows class `a` to `iv`; true if it got narrower.
    fn narrow(&mut self, a: Id, iv: Iv) -> bool {
        let a = self.find(a);
        let cur = self.classes[a as usize].iv;
        let n = meet(cur, iv);
        if n.lo > n.hi {
            self.conflict = true;
            return false;
        }
        if n == cur {
            return false;
        }
        self.classes[a as usize].iv = n;
        self.narrowed.push(a);
        true
    }

    fn union(&mut self, a: Id, b: Id) -> bool {
        let (a, b) = (self.find(a), self.find(b));
        if a == b {
            return false;
        }
        let (ia, ib) = (self.classes[a as usize].iv, self.classes[b as usize].iv);
        let iv = meet(ia, ib);
        if iv.lo > iv.hi {
            self.conflict = true;
            return false;
        }
        let size = |c: &Class| c.nodes.len() + c.parents.len();
        let (big, small) = if size(&self.classes[a as usize]) >= size(&self.classes[b as usize]) { (a, b) } else { (b, a) };
        self.parent[small as usize] = big;
        let nodes = std::mem::take(&mut self.classes[small as usize].nodes);
        let parents = std::mem::take(&mut self.classes[small as usize].parents);
        let c = &mut self.classes[big as usize];
        c.nodes.extend(nodes);
        c.parents.extend(parents);
        c.iv = iv;
        self.pending.push(big);
        if iv != ia || iv != ib {
            self.narrowed.push(big);
        }
        true
    }

    /// Restores the invariants after unions: canonical memo (merging congruent nodes),
    /// intervals propagated to parents, and pinned classes with their constant.
    fn rebuild(&mut self) {
        loop {
            if let Some(id) = self.pending.pop() {
                let id = self.find(id);
                let parents = std::mem::take(&mut self.classes[id as usize].parents);
                // (In order, so the result doesn't depend on hashing.)
                let mut kept: Vec<(ENode, Id)> = Vec::new();
                let mut at: HashMap<ENode, usize> = HashMap::new();
                for (n, p) in parents {
                    self.memo.remove(&n);
                    let n = self.canon(&n);
                    let p = self.find(p);
                    if let Some(&q) = self.memo.get(&n) {
                        self.union(p, q);
                    }
                    let p = self.find(p);
                    self.memo.insert(n, p);
                    match at.get(&n) {
                        Some(&i) => {
                            self.union(p, kept[i].1);
                            kept[i].1 = self.find(p);
                        }
                        None => {
                            at.insert(n, kept.len());
                            kept.push((n, p));
                        }
                    }
                }
                let id = self.find(id);
                self.classes[id as usize].parents.extend(kept);
                let mut seen = HashSet::new();
                let nodes: Vec<ENode> = std::mem::take(&mut self.classes[id as usize].nodes).iter().map(|n| self.canon(n)).filter(|n| seen.insert(*n)).collect();
                self.classes[id as usize].nodes = nodes;
                continue;
            }
            if let Some(id) = self.narrowed.pop() {
                let id = self.find(id);
                let iv = self.classes[id as usize].iv;
                if iv.lo == iv.hi && !self.classes[id as usize].nodes.iter().any(|n| matches!(n, ENode::Const(_))) {
                    let k = self.add(ENode::Const(iv.lo as i32));
                    self.union(id, k);
                }
                if self.budget == 0 {
                    continue;
                }
                let parents: Vec<(ENode, Id)> = self.classes[id as usize].parents.clone();
                for (n, p) in parents {
                    if self.budget == 0 {
                        break;
                    }
                    self.budget -= 1;
                    let niv = self.node_iv(&n);
                    self.narrow(p, niv);
                }
                continue;
            }
            break;
        }
    }

    fn size(&self) -> usize {
        self.memo.len()
    }

    // ------------------------------------------------------------------ rules

    /// Terms equal to class `id` (which has node `n`), by rule name.
    fn rules(&self, id: Id, n: &ENode, out: &mut Vec<(Id, T, &'static str)>) {
        let f = |x: Id| self.find(x);
        let mut push = |t: T, rule: &'static str| out.push((id, t, rule));
        match *n {
            ENode::Const(_) | ENode::Leaf(_) => {}
            ENode::Ar(op, a, b) => {
                let (ka, kb) = (self.k(a), self.k(b));
                if let (Some(x), Some(y)) = (ka, kb) {
                    push(T::K(op.apply(x, y)), "fold");
                    return;
                }
                // Identities (ir.rs `Graph::ar`), constants on either side of commutative ops.
                let sides: Vec<(Id, Id, Option<i32>)> = if op.commutative() { vec![(a, b, kb), (b, a, ka)] } else { vec![(a, b, kb)] };
                for &(x, _, k) in &sides {
                    match (op, k) {
                        (ArOp::Add | ArOp::Sub | ArOp::Or | ArOp::Xor, Some(0)) => push(T::C(x), "identity"),
                        (ArOp::Shl | ArOp::Shr, Some(k)) if k & 31 == 0 => push(T::C(x), "identity"),
                        (ArOp::Mul | ArOp::Div | ArOp::Pow, Some(1)) => push(T::C(x), "identity"),
                        (ArOp::Mul | ArOp::And, Some(0)) => push(T::K(0), "identity"),
                        (ArOp::Mod, Some(1 | -1)) => push(T::K(0), "identity"),
                        (ArOp::Pow, Some(0)) => push(T::K(1), "identity"),
                        (ArOp::And, Some(-1)) => push(T::C(x), "identity"),
                        (ArOp::And, Some(1)) if self.is_bool(x) => push(T::C(x), "identity"),
                        _ => {}
                    }
                }
                if ka == Some(0) && matches!(op, ArOp::Div | ArOp::Mod | ArOp::Shl | ArOp::Shr) {
                    push(T::K(0), "identity");
                }
                if f(a) == f(b) {
                    match op {
                        ArOp::Sub | ArOp::Xor => push(T::K(0), "identity"),
                        ArOp::And | ArOp::Or => push(T::C(a), "identity"),
                        // `x + x` is `x * 2` (one combinator either way; a wire sum can't add a
                        // value to itself, but `* 2` can be pushed into it).
                        ArOp::Add => push(ar(ArOp::Mul, T::C(a), T::K(2)), "distribute"),
                        _ => {}
                    }
                }
                // Constant chains: `(x ± c) ± k`, `(x * c) * k`, `(x & c) & k`, ….
                if let Some(k) = kb {
                    let chains: &[(ArOp, ArOp)] = match op {
                        ArOp::Add | ArOp::Sub => &[(ArOp::Add, ArOp::Add), (ArOp::Sub, ArOp::Add)],
                        ArOp::Mul => &[(ArOp::Mul, ArOp::Mul)],
                        ArOp::And => &[(ArOp::And, ArOp::And)],
                        ArOp::Or => &[(ArOp::Or, ArOp::Or)],
                        ArOp::Xor => &[(ArOp::Xor, ArOp::Xor)],
                        _ => &[],
                    };
                    for &(inner, _) in chains {
                        for (x, c) in self.ar_k(a, inner) {
                            let t = match (inner, op) {
                                (ArOp::Add | ArOp::Sub, ArOp::Add | ArOp::Sub) => {
                                    let c = if inner == ArOp::Sub { c.wrapping_neg() } else { c };
                                    let k = if op == ArOp::Sub { k.wrapping_neg() } else { k };
                                    ar(ArOp::Add, T::C(x), T::K(c.wrapping_add(k)))
                                }
                                _ => ar(op, T::C(x), T::K(op.apply(c, k))),
                            };
                            push(t, "constants");
                        }
                    }
                    // `(x >> j) >> k` is `x >> (j + k)` below 32.
                    if op == ArOp::Shr {
                        for (x, j) in self.ar_k(a, ArOp::Shr) {
                            let n = (j as u32 & 31) + (k as u32 & 31);
                            if n < 32 {
                                push(ar(ArOp::Shr, T::C(x), T::K(n as i32)), "shifts");
                            }
                        }
                    }
                    // `x - k` is `x + (-k)` (wrapping, so for every k).
                    if op == ArOp::Sub {
                        push(ar(ArOp::Add, T::C(a), T::K(k.wrapping_neg())), "constants");
                    }
                    // `(0 - x) * k` is `x * (-k)`.
                    if op == ArOp::Mul {
                        for (z, x) in self.ars(a, ArOp::Sub) {
                            if self.k(z) == Some(0) {
                                push(ar(ArOp::Mul, T::C(x), T::K(k.wrapping_neg())), "negation");
                            }
                        }
                    }
                }
                if let (ArOp::Mul, None, Some(k)) = (op, kb, ka) {
                    for (z, x) in self.ars(b, ArOp::Sub) {
                        if self.k(z) == Some(0) {
                            push(ar(ArOp::Mul, T::C(x), T::K(k.wrapping_neg())), "negation");
                        }
                    }
                }
                // `a - (a / b) * b` is `a % b` when b can't be 0, nor -1 with a = MIN (ir.rs).
                if op == ArOp::Sub {
                    for (p, q) in self.ars(b, ArOp::Mul) {
                        for (quot, d) in [(p, q), (q, p)] {
                            if self.ars(quot, ArOp::Div).iter().any(|&(x, d2)| f(x) == f(a) && f(d2) == f(d)) {
                                let (di, ai) = (self.iv(d), self.iv(a));
                                if (di.lo > 0 || di.hi < 0) && (di.lo > -1 || di.hi < -1 || ai.lo > MIN) {
                                    push(ar(ArOp::Mod, T::C(a), T::C(d)), "remainder");
                                }
                            }
                        }
                    }
                }
                if matches!(op, ArOp::Add | ArOp::Sub) {
                    self.sum_rules(op, a, b, &mut push);
                }
            }
            ENode::Cmp(op, a, b) => self.cmp_rules(op, a, b, &mut push),
            ENode::Mux(t, fc, a, b) => {
                if f(a) == f(b) {
                    push(T::C(a), "select");
                }
                match (self.k(t), self.k(fc)) {
                    (Some(k), _) => push(T::C(if k != 0 { a } else { b }), "select"),
                    (_, Some(k)) => push(T::C(if k != 0 { b } else { a }), "select"),
                    _ => {}
                }
                // `1 if t else 0` is `t` for a boolean `t`.
                match (self.k(a), self.k(b)) {
                    (Some(1), Some(0)) if self.is_bool(t) => push(T::C(t), "select"),
                    (Some(0), Some(1)) if self.is_bool(fc) => push(T::C(fc), "select"),
                    _ => {}
                }
                // An arm that is itself a select on the same condition takes its own arm.
                for (arm, other, first) in [(a, b, true), (b, a, false)] {
                    for nd in self.nodes(arm) {
                        if let ENode::Mux(t2, f2, x, y) = *nd {
                            let pick = if (f(t2), f(f2)) == (f(t), f(fc)) {
                                Some(if first { x } else { y })
                            } else if (f(t2), f(f2)) == (f(fc), f(t)) {
                                Some(if first { y } else { x })
                            } else {
                                None
                            };
                            if let Some(p) = pick {
                                let t = if first { mux(t, fc, T::C(p), T::C(other)) } else { mux(t, fc, T::C(other), T::C(p)) };
                                push(t, "nested select");
                            }
                        }
                    }
                }
                // Arms with a common operand: `op(x, p) if c else op(x, q)` is
                // `op(x, p if c else q)` (exactly one arm is taken); `x ± d if c else x` is
                // `x ± (d if c else 0)` (ir.rs `mux_factor`).
                let arms_a: Vec<ENode> = self.nodes(a).to_vec();
                let arms_b: Vec<ENode> = self.nodes(b).to_vec();
                for na in &arms_a {
                    for nb in &arms_b {
                        if let (ENode::Ar(o1, x1, y1), ENode::Ar(o2, x2, y2)) = (*na, *nb) {
                            if o1 != o2 {
                                continue;
                            }
                            if f(x1) == f(x2) {
                                push(ar(o1, T::C(x1), mux(t, fc, T::C(y1), T::C(y2))), "factor select");
                            }
                            if f(y1) == f(y2) {
                                push(ar(o1, mux(t, fc, T::C(x1), T::C(x2)), T::C(y1)), "factor select");
                            }
                            if o1.commutative() {
                                if f(x1) == f(y2) {
                                    push(ar(o1, T::C(x1), mux(t, fc, T::C(y1), T::C(x2))), "factor select");
                                }
                                if f(y1) == f(x2) {
                                    push(ar(o1, T::C(y1), mux(t, fc, T::C(x1), T::C(y2))), "factor select");
                                }
                            }
                        }
                    }
                }
                for (arm, other, first) in [(a, b, true), (b, a, false)] {
                    let pick = |d: T| if first { mux(t, fc, d, T::K(0)) } else { mux(t, fc, T::K(0), d) };
                    for nd in self.nodes(arm) {
                        match *nd {
                            ENode::Ar(ArOp::Add, x, y) if f(x) == f(other) => push(ar(ArOp::Add, T::C(other), pick(T::C(y))), "factor select"),
                            ENode::Ar(ArOp::Add, x, y) if f(y) == f(other) => push(ar(ArOp::Add, T::C(other), pick(T::C(x))), "factor select"),
                            ENode::Ar(ArOp::Sub, x, y) if f(x) == f(other) => push(ar(ArOp::Sub, T::C(other), pick(T::C(y))), "factor select"),
                            _ => {}
                        }
                    }
                }
            }
        }
    }

    /// Sums: negations, distribution, constants moved outwards.
    fn sum_rules(&self, op: ArOp, a: Id, b: Id, push: &mut impl FnMut(T, &'static str)) {
        let f = |x: Id| self.find(x);
        let neg = |x: Id| -> Vec<Id> { self.ars(x, ArOp::Sub).into_iter().filter(|&(z, _)| self.k(z) == Some(0)).map(|(_, y)| y).collect() };
        // `a + (0 - y)` is `a - y`; `a - (0 - y)` is `a + y`.
        let flip = if op == ArOp::Add { ArOp::Sub } else { ArOp::Add };
        for y in neg(b) {
            push(ar(flip, T::C(a), T::C(y)), "negation");
        }
        if op == ArOp::Add {
            for y in neg(a) {
                push(ar(ArOp::Sub, T::C(b), T::C(y)), "negation");
            }
        }
        // `x * p ± x * q` is `x * (p ± q)`, `x * p ± x` is `x * (p ± 1)` (wrapping).
        let muls = |v: Id| -> Vec<(Id, i32)> {
            let mut m = self.ar_k(v, ArOp::Mul);
            m.push((v, 1));
            m
        };
        let comb = |p: i32, q: i32| if op == ArOp::Add { p.wrapping_add(q) } else { p.wrapping_sub(q) };
        for (x, p) in muls(a) {
            for (y, q) in muls(b) {
                if f(x) == f(y) && (p, q) != (1, 1) {
                    push(ar(ArOp::Mul, T::C(x), T::K(comb(p, q))), "distribute");
                }
            }
        }
        // Constants move outwards, so they can meet: `(x + c) + y` is `(x + y) + c`,
        // `(x + c) - y` is `(x - y) + c`, `y - (x + c)` is `(y - x) + (-c)`.
        if self.k(b).is_none() {
            for (x, c) in self.ar_k(a, ArOp::Add) {
                push(ar(ArOp::Add, ar(op, T::C(x), T::C(b)), T::K(c)), "constants");
            }
        }
        if self.k(a).is_none() {
            for (x, c) in self.ar_k(b, ArOp::Add) {
                let c = if op == ArOp::Sub { c.wrapping_neg() } else { c };
                push(ar(ArOp::Add, ar(op, T::C(a), T::C(x)), T::K(c)), "constants");
            }
        }
    }

    /// Comparisons: canonical order, offsets, negations, differences, scaled values.
    fn cmp_rules(&self, op: CmpOp, a: Id, b: Id, push: &mut impl FnMut(T, &'static str)) {
        let (ka, kb) = (self.k(a), self.k(b));
        if let (Some(x), Some(y)) = (ka, kb) {
            push(T::K(op.apply(x, y) as i32), "fold");
            return;
        }
        // Constants second (deciders compare a signal with something).
        if ka.is_some() {
            push(cmp(op.flip(), T::C(b), T::C(a)), "flip");
            return;
        }
        if matches!(op, CmpOp::Eq | CmpOp::Ne) && kb.is_none() {
            push(cmp(op, T::C(b), T::C(a)), "flip");
        }
        let eq = matches!(op, CmpOp::Eq | CmpOp::Ne);
        let Some(c) = kb else {
            // `x - y op 0`-like forms need a constant; `(x - y) op z` stays.
            return;
        };
        let c64 = c as i64;
        // `bool != 0`, `bool == 1`, `bool > 0` are the bool; `bool == 0` (`<= 0`, `< 1`) of a
        // comparison is the negated comparison.
        if self.is_bool(a) {
            if matches!((op, c), (CmpOp::Ne, 0) | (CmpOp::Eq, 1) | (CmpOp::Gt, 0) | (CmpOp::Ge, 1)) {
                push(T::C(a), "boolean");
            }
            if matches!((op, c), (CmpOp::Eq, 0) | (CmpOp::Le, 0) | (CmpOp::Lt, 1) | (CmpOp::Ne, 1)) {
                for nd in self.nodes(a) {
                    if let ENode::Cmp(o2, x, y) = *nd {
                        push(cmp(o2.negate(), T::C(x), T::C(y)), "boolean");
                    }
                }
            }
        }
        // `x + k op c` is `x op c - k`: always for == and != (wrapping both sides), for order
        // only if `x + k` can't wrap (ir.rs `Graph::cmp`).
        for (x, k) in self.ar_k(a, ArOp::Add).into_iter().chain(self.ar_k(a, ArOp::Sub).into_iter().map(|(x, k)| (x, k.wrapping_neg()))) {
            let xi = self.iv(x);
            let k64 = k as i64;
            if eq {
                push(cmp(op, T::C(x), T::K(c.wrapping_sub(k))), "offset");
            } else if fits(xi.lo + k64) && fits(xi.hi + k64) && fits(c64 - k64) {
                push(cmp(op, T::C(x), T::K((c64 - k64) as i32)), "offset");
            }
        }
        // `k - x op c` is `x flip(op) k - c` (the same, if `k - x` can't wrap, for order).
        for (kv, x) in self.ars(a, ArOp::Sub) {
            let Some(k) = self.k(kv) else { continue };
            if self.k(x).is_some() {
                continue;
            }
            let (xi, k64) = (self.iv(x), k as i64);
            if eq {
                push(cmp(op, T::C(x), T::K(k.wrapping_sub(c))), "negation");
            } else if fits(k64 - xi.hi) && fits(k64 - xi.lo) && fits(k64 - c64) {
                push(cmp(op.flip(), T::C(x), T::K((k64 - c64) as i32)), "negation");
            }
        }
        // `x - y op 0` is `x op y` (for order: if `x - y` can't wrap); `x ^ y == 0` is `x == y`.
        if c == 0 {
            for (x, y) in self.ars(a, ArOp::Sub) {
                if self.k(x).is_some() || self.k(y).is_some() {
                    continue;
                }
                let (xi, yi) = (self.iv(x), self.iv(y));
                if eq || (fits(xi.lo - yi.hi) && fits(xi.hi - yi.lo)) {
                    push(cmp(op, T::C(x), T::C(y)), "difference");
                }
            }
            if eq {
                for (x, y) in self.ars(a, ArOp::Xor) {
                    push(cmp(op, T::C(x), T::C(y)), "difference");
                }
            }
        }
        // `x * k op c` with k > 0 and `x * k` not wrapping compares `x` with a bound.
        for (x, k) in self.ar_k(a, ArOp::Mul) {
            let (xi, k64) = (self.iv(x), k as i64);
            if k <= 0 || !fits(xi.lo * k64) || !fits(xi.hi * k64) {
                continue;
            }
            let (fl, fl1) = (c64.div_euclid(k64), (c64 - 1).div_euclid(k64));
            if !fits(fl) || !fits(fl1) {
                continue;
            }
            let t = match op {
                CmpOp::Lt => cmp(CmpOp::Le, T::C(x), T::K(fl1 as i32)),
                CmpOp::Le => cmp(CmpOp::Le, T::C(x), T::K(fl as i32)),
                CmpOp::Gt => cmp(CmpOp::Gt, T::C(x), T::K(fl as i32)),
                CmpOp::Ge => cmp(CmpOp::Gt, T::C(x), T::K(fl1 as i32)),
                CmpOp::Eq | CmpOp::Ne if c64 % k64 != 0 => T::K((op == CmpOp::Ne) as i32),
                CmpOp::Eq | CmpOp::Ne => cmp(op, T::C(x), T::K((c64 / k64) as i32)),
            };
            push(t, "scaled");
        }
    }
}

// ------------------------------------------------------------------ extraction

/// Whether a value computed by node `n` can write a wire sum's signal (and take a factor).
fn sum_part(g: &Graph, n: &ENode) -> bool {
    match *n {
        ENode::Ar(..) | ENode::Cmp(..) | ENode::Mux(..) => true,
        ENode::Leaf(v) => matches!(g.op(v), Op::Dec(_) | Op::Sel(_) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_)),
        ENode::Const(_) => false,
    }
}

const SIZE_BITS: u32 = 24;

fn cost(combs: u64, size: u64) -> u64 {
    combs.saturating_mul(1 << SIZE_BITS).saturating_add(size.min((1 << SIZE_BITS) - 1))
}

impl EGraph<'_> {
    /// The cheapest node of every class (tree costs: combinators, then size).
    fn extract(&self) -> HashMap<Id, (u64, ENode)> {
        let mut best: HashMap<Id, (u64, ENode)> = HashMap::new();
        let classes: Vec<Id> = (0..self.classes.len() as Id).filter(|&c| self.find(c) == c).collect();
        // Classes are mostly in creation order, operands first, so this settles in a few
        // passes; a class left without a cost just isn't rebuilt (the unit stays as it is).
        for _ in 0..64 {
            let mut changed = false;
            for &c in &classes {
                for n in &self.classes[c as usize].nodes {
                    let Some(x) = self.node_cost(n, &best) else { continue };
                    if best.get(&c).is_none_or(|b| x < b.0) {
                        best.insert(c, (x, *n));
                        changed = true;
                    }
                }
            }
            if !changed {
                break;
            }
        }
        best
    }

    fn node_cost(&self, n: &ENode, best: &HashMap<Id, (u64, ENode)>) -> Option<u64> {
        let get = |c: Id| best.get(&self.find(c)).copied();
        let split = |x: u64| (x >> SIZE_BITS, x & ((1 << SIZE_BITS) - 1));
        let (mut combs, mut size) = (0u64, 1u64);
        let mut kid = |c: Id, inline: bool| -> Option<ENode> {
            let (x, node) = get(c)?;
            // A condition tested by the select's deciders: only its operands are built.
            if let (true, ENode::Cmp(_, p, q)) = (inline, node) {
                for o in [p, q] {
                    let (oc, os) = split(get(o)?.0);
                    combs += oc;
                    size += os;
                }
                return Some(node);
            }
            let (xc, xs) = split(x);
            combs += xc;
            size += xs;
            Some(node)
        };
        let own: u64 = match *n {
            ENode::Const(_) | ENode::Leaf(_) => 0,
            ENode::Cmp(_, a, b) => {
                kid(a, false)?;
                kid(b, false)?;
                1
            }
            ENode::Mux(t, f, a, b) => {
                kid(t, true)?;
                kid(f, true)?;
                kid(a, false)?;
                kid(b, false)?;
                (self.k(a) != Some(0)) as u64 + (self.k(b) != Some(0)) as u64
            }
            ENode::Ar(op, a, b) => {
                let na = kid(a, false)?;
                let nb = kid(b, false)?;
                match op {
                    ArOp::Add | ArOp::Sub if self.find(a) != self.find(b) && sum_part(self.g, &na) && sum_part(self.g, &nb) => 0,
                    ArOp::Mul => {
                        let x = if self.k(b).is_some() { Some(na) } else if self.k(a).is_some() { Some(nb) } else { None };
                        match x {
                            Some(ENode::Cmp(..) | ENode::Mux(..) | ENode::Ar(ArOp::Add | ArOp::Sub, ..)) => 0,
                            Some(ENode::Leaf(v)) if sum_part(self.g, &ENode::Leaf(v)) => 0,
                            _ => 1,
                        }
                    }
                    _ => 1,
                }
            }
        };
        Some(cost(combs + own, size))
    }
}

// ------------------------------------------------------------------ the graph's cost

/// Combinators `codegen::logic` would build for the scalar logic reachable from `roots`,
/// roughly (see the module docs): wire sums of single-use operands, `* k` pushed into a
/// single-use operand, conditions only used by selects, a decider per select arm.
pub fn graph_cost(g: &Graph, roots: &[V]) -> u64 {
    let live = g.reachable(roots);
    let is_root: HashSet<V> = roots.iter().copied().collect();
    let mut users: HashMap<V, Vec<V>> = HashMap::new();
    for &v in &live {
        let mut ops = g.operands(v);
        ops.sort_unstable();
        ops.dedup();
        for o in ops {
            users.entry(o).or_default().push(v);
        }
    }
    let single = |v: V| !is_root.contains(&v) && users.get(&v).is_some_and(|u| u.len() == 1);
    let part = |v: V| single(v) && matches!(g.op(v), Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) | Op::Sel(_) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_));
    let mut total = 0u64;
    for &v in &live {
        total += match *g.op(v) {
            Op::Const(_) | Op::Src(_) | Op::Each(_) | Op::SigK(_) | Op::BConst(_) | Op::SigOf(_) => 0,
            Op::Cmp(..) => {
                let cond_only = !is_root.contains(&v)
                    && users.get(&v).is_some_and(|us| us.iter().all(|&u| match *g.op(u) {
                        Op::Mux { t, f, a, b } => (t == v || f == v) && a != v && b != v,
                        _ => false,
                    }));
                (!cond_only) as u64
            }
            Op::Mux { a, b, .. } => (g.as_const(a) != Some(0)) as u64 + (g.as_const(b) != Some(0)) as u64,
            Op::Dec(ref arms) => arms.len() as u64,
            Op::Sel(ref arms) => arms.iter().filter(|(_, x)| g.as_const(*x) != Some(0)).count() as u64,
            Op::Ar(ArOp::Add | ArOp::Sub, a, b) if a != b && part(a) && part(b) => 0,
            Op::Ar(ArOp::Mul, a, b) if g.as_const(a).is_some() != g.as_const(b).is_some() => {
                let x = if g.as_const(b).is_some() { a } else { b };
                let push = single(x) && matches!(g.op(x), Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) | Op::Sel(_) | Op::Ar(ArOp::Add | ArOp::Sub, ..) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_));
                (!push) as u64
            }
            _ => 1,
        };
    }
    total
}

/// Depth of each node reachable from `roots` (sources and constants 0), like
/// [`Graph::depths`] but only over what `roots` need.
fn depths(g: &Graph, roots: &[V]) -> HashMap<V, u32> {
    let mut d = HashMap::new();
    for v in g.reachable(roots) {
        let ops = g.operands(v);
        let x = if ops.is_empty() { 0 } else { 1 + ops.iter().map(|o| d.get(o).copied().unwrap_or(0)).max().unwrap() };
        d.insert(v, x);
    }
    d
}

// ------------------------------------------------------------------ the pass

/// Whether `v` is scalar arithmetic, a comparison or a select the e-graph may rewrite.
fn rewritable(g: &Graph, v: V) -> bool {
    let scalar = |o: V| !g.is_bundle(o) && !g.is_sigval(o) && g.as_sig(o).is_none();
    let ok = match *g.op(v) {
        Op::Ar(_, a, b) | Op::Cmp(_, a, b) => scalar(a) && scalar(b),
        Op::Mux { t, f, a, b } => [t, f, a, b].into_iter().all(scalar),
        _ => false,
    };
    ok && scalar(v) && !g.uses_each(v)
}

/// Optimises the scalar logic reachable from `roots` (see the module docs). Returns the new
/// root of each root (the same node where nothing changed), or `None` if the unit is kept as
/// it is. Roots marked in `no_const` (conditions and checks, which lowering only makes for
/// non-constants) keep their node rather than become a constant.
pub fn optimize(g: &mut Graph, roots: &[V], no_const: &[bool], what: &str) -> Option<Vec<V>> {
    if !enabled() {
        return None;
    }
    run(g, roots, no_const, what, false)
}

/// [`optimize`]; with `force`, the extracted forms are returned even if they aren't cheaper
/// (tests check every rewrite that way).
fn run(g: &mut Graph, roots: &[V], no_const: &[bool], what: &str, force: bool) -> Option<Vec<V>> {
    if roots.is_empty() {
        return None;
    }
    let t0 = crate::clock::Instant::now();
    // The region: rewritable nodes reachable from the roots through rewritable nodes.
    let mut region: HashSet<V> = HashSet::new();
    let mut stack: Vec<V> = roots.iter().copied().filter(|&r| rewritable(g, r)).collect();
    while let Some(v) = stack.pop() {
        if !region.insert(v) {
            continue;
        }
        if region.len() > MAX_UNIT {
            return None;
        }
        stack.extend(g.operands(v).into_iter().filter(|&o| rewritable(g, o) && !region.contains(&o)));
    }
    if region.is_empty() {
        return None;
    }
    let mut order: Vec<V> = region.iter().copied().collect();
    order.sort_unstable(); // operands are created before their users
    let (new_roots, stats) = {
        let gr: &Graph = g;
        let mut eg = EGraph::new(gr);
        let mut id_of: HashMap<V, Id> = HashMap::new();
        let leaf = |eg: &mut EGraph, id_of: &mut HashMap<V, Id>, v: V| -> Id {
            if let Some(&i) = id_of.get(&v) {
                return i;
            }
            let i = match gr.as_const(v) {
                Some(k) => eg.add(ENode::Const(k)),
                None => eg.add(ENode::Leaf(v)),
            };
            id_of.insert(v, i);
            i
        };
        for &v in &order {
            let mut opd = |o: V| if region.contains(&o) { id_of[&o] } else { leaf(&mut eg, &mut id_of, o) };
            let n = match *gr.op(v) {
                Op::Ar(op, a, b) => ENode::Ar(op, opd(a), opd(b)),
                Op::Cmp(op, a, b) => ENode::Cmp(op, opd(a), opd(b)),
                Op::Mux { t, f, a, b } => ENode::Mux(opd(t), opd(f), opd(a), opd(b)),
                _ => unreachable!("not rewritable"),
            };
            let i = eg.add(n);
            eg.narrow(i, gr.iv(v));
            id_of.insert(v, i);
        }
        eg.budget = 20 * order.len() + 1000;
        eg.rebuild();
        let limit = node_limit(order.len());
        let mut fired: HashMap<&'static str, usize> = HashMap::new();
        let mut iters = 0;
        for _ in 0..MAX_ITERS {
            iters += 1;
            let mut found = Vec::new();
            for c in 0..eg.classes.len() as Id {
                if eg.find(c) != c {
                    continue;
                }
                for n in eg.classes[c as usize].nodes.clone() {
                    eg.rules(c, &n, &mut found);
                }
            }
            let mut any = false;
            for (id, t, rule) in found {
                if eg.size() >= limit {
                    break;
                }
                let before = eg.size();
                let r = eg.add_term(&t);
                if eg.union(id, r) || eg.size() > before {
                    *fired.entry(rule).or_default() += 1;
                    any = true;
                }
            }
            eg.rebuild();
            if eg.conflict || !any || eg.size() >= limit {
                break;
            }
        }
        if eg.conflict {
            if stats_on() {
                eprintln!("egraph {what}: interval conflict, unit left alone");
            }
            return None;
        }
        let best = eg.extract();
        let root_ids: Vec<Option<Id>> = roots.iter().map(|r| region.contains(r).then(|| eg.find(id_of[r]))).collect();
        let picks: HashMap<Id, ENode> = best.iter().map(|(&c, &(_, n))| (c, n)).collect();
        let ivs: HashMap<Id, Iv> = picks.keys().map(|&c| (c, eg.iv(c))).collect();
        let finds: Vec<Id> = (0..eg.classes.len() as Id).map(|c| eg.find(c)).collect();
        let stats = (order.len(), eg.size(), iters, fired);
        ((root_ids, picks, ivs, finds), stats)
    };
    let (root_ids, picks, ivs, finds) = new_roots;
    // Rebuild the chosen forms with the ordinary constructors.
    let mut built: HashMap<Id, V> = HashMap::new();
    let mut out = Vec::with_capacity(roots.len());
    for (r, id) in roots.iter().zip(&root_ids) {
        match id {
            None => out.push(*r),
            Some(id) => {
                let mut on_stack = HashSet::new();
                match build(g, *id, &picks, &ivs, &finds, &mut built, &mut on_stack) {
                    Some(v) => out.push(v),
                    None => {
                        if stats_on() {
                            eprintln!("egraph {what}: no acyclic form extracted, unit left alone");
                        }
                        return None;
                    }
                }
            }
        }
    }
    for (i, (r, n)) in roots.iter().zip(out.iter_mut()).enumerate() {
        if no_const.get(i).copied().unwrap_or(false) && g.as_const(*n).is_some() && g.as_const(*r).is_none() {
            *n = *r;
        }
    }
    let (before, after) = (graph_cost(g, roots), graph_cost(g, &out));
    let (d0, d1) = (depths(g, roots), depths(g, &out));
    let deeper = roots.iter().zip(&out).any(|(r, n)| d1[n] > d0[r]);
    let keep = force || (after < before && !deeper);
    if stats_on() {
        let (n, size, iters, fired) = &stats;
        let mut fired: Vec<_> = fired.iter().collect();
        fired.sort();
        eprintln!(
            "egraph {what}: {n} nodes -> {size} e-nodes, {iters} rounds, {:?}; cost {before} -> {after}{}{}; {:.1} ms",
            fired,
            if deeper { ", deeper" } else { "" },
            if keep { ", kept" } else { "" },
            t0.elapsed().as_secs_f64() * 1000.0
        );
    }
    if !keep {
        return None;
    }
    for (r, n) in roots.iter().zip(&out) {
        if r != n {
            g.tv_claim_same(*r, *n);
        }
    }
    CHANGED.with(|c| c.set(c.get() + 1));
    Some(out)
}

/// Builds class `id`'s chosen form; `None` on a cycle.
fn build(g: &mut Graph, id: Id, picks: &HashMap<Id, ENode>, ivs: &HashMap<Id, Iv>, finds: &[Id], built: &mut HashMap<Id, V>, on_stack: &mut HashSet<Id>) -> Option<V> {
    let id = finds[id as usize];
    if let Some(&v) = built.get(&id) {
        return Some(v);
    }
    if !on_stack.insert(id) {
        return None;
    }
    let n = *picks.get(&id)?;
    let mut kid = |c: Id, g: &mut Graph| build(g, c, picks, ivs, finds, built, on_stack);
    let v = match n {
        ENode::Const(k) => g.konst(k),
        ENode::Leaf(v) => v,
        ENode::Ar(op, a, b) => {
            let (a, b) = (kid(a, g)?, kid(b, g)?);
            g.lookup(&Op::Ar(op, a, b)).unwrap_or_else(|| g.ar(op, a, b))
        }
        ENode::Cmp(op, a, b) => {
            let (a, b) = (kid(a, g)?, kid(b, g)?);
            g.lookup(&Op::Cmp(op, a, b)).unwrap_or_else(|| g.cmp(op, a, b))
        }
        ENode::Mux(t, f, a, b) => {
            let (t, f, a, b) = (kid(t, g)?, kid(f, g)?, kid(a, g)?, kid(b, g)?);
            g.lookup(&Op::Mux { t, f, a, b }).unwrap_or_else(|| g.mux_tf(t, f, a, b))
        }
    };
    on_stack.remove(&id);
    // The node is the class's value everywhere, so the class's bounds hold for it.
    if matches!(g.op(v), Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. }) {
        g.narrow(v, ivs[&id]);
    }
    built.insert(id, v);
    Some(v)
}

impl Graph {
    /// Logs that `new` computes the same value as `old` (an e-graph rewrite of a root).
    fn tv_claim_same(&mut self, old: V, new: V) {
        if self.tv.on {
            self.tv_claim("egraph", Req::Same(old), new);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ticky_factorio::{ArOp, CmpOp};

    /// xorshift64*
    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            self.0 ^= self.0 >> 12;
            self.0 ^= self.0 << 25;
            self.0 ^= self.0 >> 27;
            self.0.wrapping_mul(0x2545F4914F6CDD1D)
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
        fn pick<T: Copy>(&mut self, xs: &[T]) -> T {
            xs[self.below(xs.len())]
        }
    }

    fn eval(g: &Graph, v: V, input: &[i32], memo: &mut HashMap<V, i32>) -> i32 {
        if let Some(&x) = memo.get(&v) {
            return x;
        }
        let x = match *g.op(v) {
            Op::Const(k) => k,
            Op::Src(s) => input[s as usize],
            Op::Ar(op, a, b) => op.apply(eval(g, a, input, memo), eval(g, b, input, memo)),
            Op::Cmp(op, a, b) => op.apply(eval(g, a, input, memo), eval(g, b, input, memo)) as i32,
            Op::Mux { t, f, a, b } => {
                let (t, f) = (eval(g, t, input, memo), eval(g, f, input, memo));
                assert!((t != 0) != (f != 0), "select conditions not complementary");
                let x = if t != 0 { eval(g, a, input, memo) } else { 0 };
                x.wrapping_add(if f != 0 { eval(g, b, input, memo) } else { 0 })
            }
            ref op => panic!("unexpected {op:?}"),
        };
        memo.insert(v, x);
        x
    }

    const KS: [i32; 14] = [0, 1, -1, 2, 3, 5, -3, 7, 16, 100, -100, i32::MAX, i32::MIN, 31];

    /// A random scalar expression over the sources, shaped to meet the rules.
    fn expr(g: &mut Graph, rng: &mut Rng, srcs: &[V], depth: u32) -> V {
        if depth == 0 || rng.below(5) == 0 {
            return if rng.below(4) == 0 { g.konst(rng.pick(&KS)) } else { rng.pick(srcs) };
        }
        let sub = |g: &mut Graph, rng: &mut Rng| expr(g, rng, srcs, depth - 1);
        match rng.below(9) {
            0..=3 => {
                let op = rng.pick(&[ArOp::Add, ArOp::Sub, ArOp::Mul, ArOp::Add, ArOp::Sub, ArOp::Xor, ArOp::And, ArOp::Shr, ArOp::Div, ArOp::Mod, ArOp::Or]);
                let a = sub(g, rng);
                let b = if rng.below(2) == 0 { g.konst(rng.pick(&KS)) } else { sub(g, rng) };
                let (a, b) = if rng.below(4) == 0 { (b, a) } else { (a, b) };
                g.ar(op, a, b)
            }
            4 => {
                // `x * k ± x` or `x * k ± x * k` (distribution, cancellation).
                let x = sub(g, rng);
                let k = g.konst(rng.pick(&KS));
                let p = g.ar(ArOp::Mul, x, k);
                let op = rng.pick(&[ArOp::Add, ArOp::Sub]);
                let y = if rng.below(2) == 0 { x } else { p };
                g.ar(op, p, y)
            }
            5 | 6 => {
                let op = rng.pick(&[CmpOp::Lt, CmpOp::Gt, CmpOp::Eq, CmpOp::Ge, CmpOp::Le, CmpOp::Ne]);
                let a = sub(g, rng);
                let b = if rng.below(3) > 0 { g.konst(rng.pick(&KS)) } else { sub(g, rng) };
                let (a, b) = if rng.below(4) == 0 { (b, a) } else { (a, b) };
                g.cmp(op, a, b)
            }
            _ => {
                let c = sub(g, rng);
                let x = sub(g, rng);
                let (a, b) = match rng.below(3) {
                    // Arms sharing an operand.
                    0 => {
                        let op = rng.pick(&[ArOp::Add, ArOp::Sub, ArOp::Mul, ArOp::Xor]);
                        let (p, q) = (sub(g, rng), sub(g, rng));
                        (g.ar(op, x, p), g.ar(op, x, q))
                    }
                    // A nested select on the same condition.
                    1 => {
                        let y = sub(g, rng);
                        (g.mux(c, x, y), sub(g, rng))
                    }
                    _ => (x, sub(g, rng)),
                };
                g.mux(c, a, b)
            }
        }
    }

    /// Every rewrite, forced through whatever the cost: old and new roots agree on edge-case
    /// and random inputs within the sources' intervals.
    #[test]
    fn rewrites_keep_values() {
        let mut rng = Rng(0x9E3779B97F4A7C15);
        let ivs = [Iv::FULL, Iv { lo: 0, hi: 100 }, Iv { lo: -50, hi: 50 }, Iv { lo: 0, hi: 1 }];
        let mut changed = 0;
        for round in 0..400 {
            let mut g = Graph::new(ivs.to_vec());
            let srcs: Vec<V> = (0..ivs.len() as u32).map(|s| g.src(s)).collect();
            let roots: Vec<V> = (0..4).map(|_| expr(&mut g, &mut rng, &srcs, 4)).collect();
            let no_const = vec![false; roots.len()];
            let Some(new) = run(&mut g, &roots, &no_const, "test", true) else { continue };
            if new != roots {
                changed += 1;
            }
            let edge = |iv: Iv| -> Vec<i32> { [iv.lo, iv.lo + 1, -1, 0, 1, 2, iv.hi - 1, iv.hi].into_iter().filter(|x| iv.lo <= *x && *x <= iv.hi).map(|x| x as i32).collect() };
            for i in 0..300 {
                let input: Vec<i32> = ivs
                    .iter()
                    .map(|&iv| {
                        if i % 2 == 0 {
                            let e = edge(iv);
                            e[rng.below(e.len())]
                        } else {
                            (iv.lo + (rng.next() % (iv.hi - iv.lo + 1) as u64) as i64) as i32
                        }
                    })
                    .collect();
                let (mut m0, mut m1) = (HashMap::new(), HashMap::new());
                for (r, n) in roots.iter().zip(&new) {
                    let (x, y) = (eval(&g, *r, &input, &mut m0), eval(&g, *n, &input, &mut m1));
                    assert_eq!(x, y, "round {round}: root %{r} {:?} vs %{n} {:?} on {input:?}", g.op(*r), g.op(*n));
                }
            }
        }
        assert!(changed > 100, "only {changed} graphs changed");
    }

    #[test]
    fn finds_cheaper_forms() {
        let mut g = Graph::new(vec![Iv::FULL, Iv::FULL, Iv { lo: 0, hi: 1000 }]);
        let (x, y, n) = (g.src(0), g.src(1), g.src(2));
        let m1 = g.konst(-1);
        // `b = y * -1; b += b` is `y * -2`.
        let b = g.ar(ArOp::Mul, y, m1);
        let bb = g.ar(ArOp::Add, b, b);
        // `x - y == 0` is `x == y`.
        let d = g.ar(ArOp::Sub, x, y);
        let z = g.konst(0);
        let eq = g.cmp(CmpOp::Eq, d, z);
        // `n * 4 < 10` is `n <= 2` (no wrap within 0..1000).
        let four = g.konst(4);
        let ten = g.konst(10);
        let n4 = g.ar(ArOp::Mul, n, four);
        let lt = g.cmp(CmpOp::Lt, n4, ten);
        let roots = [bb, eq, lt];
        let new = optimize(&mut g, &roots, &[false; 3], "test").expect("cheaper");
        assert!(matches!(*g.op(new[0]), Op::Ar(ArOp::Mul, a, k) if a == y && g.as_const(k) == Some(-2)), "{:?}", g.op(new[0]));
        assert!(matches!(*g.op(new[1]), Op::Cmp(CmpOp::Eq, a, b) if (a, b) == (x, y) || (a, b) == (y, x)), "{:?}", g.op(new[1]));
        assert!(matches!(*g.op(new[2]), Op::Cmp(CmpOp::Le, a, k) if a == n && g.as_const(k) == Some(2)), "{:?}", g.op(new[2]));
        assert!(graph_cost(&g, &new) < graph_cost(&g, &roots));
    }

    /// Ordered comparisons that could wrap stay as they are.
    #[test]
    fn wrapping_comparisons_stay() {
        let mut g = Graph::new(vec![Iv::FULL]);
        let x = g.src(0);
        let (one, five, four) = (g.konst(1), g.konst(5), g.konst(4));
        let x1 = g.ar(ArOp::Add, x, one);
        let c = g.cmp(CmpOp::Lt, x1, five);
        let x4 = g.ar(ArOp::Mul, x, four);
        let d = g.cmp(CmpOp::Gt, x4, five);
        let roots = [c, d];
        let new = run(&mut g, &roots, &[false; 2], "test", true).unwrap();
        assert_eq!(new, roots.to_vec());
    }
}
