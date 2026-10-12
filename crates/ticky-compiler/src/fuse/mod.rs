//! Fusion, run after lowering:
//!
//! * Boolean logic (comparisons combined with `and`/`or`/`not`, selects between constants)
//!   becomes multi-condition deciders: a decider evaluates an OR of AND-terms in one tick.
//! * A register update becomes a set of *guarded loads*: `x = a if c else x` loads `a` when
//!   `c` holds and otherwise keeps `x`, with no select stage at all.
//! * Branch and wait conditions keep their condition lists so they can be folded straight
//!   into the deciders that commit a step or choose the next one.
//!
//! Layout: this file has the plan types, DNF helpers and the core of [`Fuser`] (`dnf`,
//! `rebuild`, conditions). `plans.rs` splits register updates into guarded loads. Pattern
//! rewrites live one per file: `lookups.rs` (table lookups, picks among bundle reads, shared
//! index wires), `counts.rs` (counting matches), `argmax.rs` (running maximum), `writes.rs`
//! (combined bundle writes), `sortnet.rs` (sorting networks, order statistics). Add new pattern
//! rewrites as their own file here, as an `impl Fuser<'_>` block, hooked in from
//! [`Fuser::rebuild`] (or `Fuser::split` for register loads).

mod argmax;
mod boolean;
pub(crate) use boolean::simplify_terms;
mod counts;
mod lookups;
mod plans;
mod sortnet;
mod writes;

pub use plans::keep_of;

use std::collections::HashMap;

use ticky_factorio::{ArOp, CmpOp};

use crate::ir::{dnf_operands, BLit, BOp, BTerm, Dnf, Graph, Iv, Lit, Op, V};

/// Most guarded loads one register update is split into.
const MAX_LOADS: usize = 8;

/// Most arms a tree of bundle selects is flattened into.
const MAX_ARMS: usize = 8;

/// Upper bounds on a fused condition, to keep deciders reasonable.
const MAX_TERMS: usize = 12;
const MAX_LITS: usize = 32;

#[derive(Clone, PartialEq, Eq, Debug)]
pub enum LoadVal {
    Const(i32),
    Node(V),
}

/// Load `val` into a register when `guard` holds at commit time. `guard == [[]]` is
/// unconditional. A `Const(0)` load writes nothing but still stops the register holding.
///
/// A *direct* load is a constant whose guard is checked by the load decider itself, on the
/// commit tick (codegen also makes staged values direct: `registers::stage_loads`). Other
/// guarded loads first compute an enable pulse one tick earlier.
#[derive(Clone, Debug)]
pub struct Load {
    pub guard: Dnf,
    pub val: LoadVal,
    pub direct: bool,
}

/// How one writer (an `every` block or a main-program step) updates a register.
#[derive(Clone, Debug)]
pub struct WriterPlan {
    pub loads: Vec<Load>,
    /// For direct loads: the condition under which none of them fires (so the register may
    /// hold). `None` when there are no direct loads.
    pub keep: Option<Dnf>,
}

impl WriterPlan {
    /// Ticks after the step/iteration starts at which everything this plan reads is ready.
    pub fn ready(&self, depths: &[u32]) -> u32 {
        let mut r = 0;
        for l in &self.loads {
            let rg = ready_depth(depths, dnf_operands(&l.guard));
            let t = match (&l.val, l.direct, is_true(&l.guard)) {
                (LoadVal::Node(v), true, _) => depths[*v as usize].max(rg),
                (_, true, _) => rg,
                (LoadVal::Node(v), _, true) => depths[*v as usize],
                (LoadVal::Const(_), _, true) => 0,
                (LoadVal::Node(v), false, false) => depths[*v as usize].max(rg + 1),
                (LoadVal::Const(_), false, false) => rg + 1,
            };
            r = r.max(t);
        }
        r
    }

    pub fn operands(&self) -> Vec<V> {
        let mut out = load_operands(&self.loads);
        if let Some(k) = &self.keep {
            out.extend(dnf_operands(k));
        }
        out
    }
}

/// A branch or wait condition: its node, and (when small enough) its condition lists.
#[derive(Clone, Debug)]
pub struct CondPlan {
    pub node: V,
    pub pos: Option<Dnf>,
    pub neg: Option<Dnf>,
}

pub fn is_true(d: &Dnf) -> bool {
    d.iter().any(|t| t.is_empty())
}

fn size_ok(d: &Dnf) -> bool {
    d.len() <= MAX_TERMS && d.iter().map(|t| t.len()).sum::<usize>() <= MAX_LITS
}

fn negated(l: Lit) -> Lit {
    Lit { op: l.op.negate(), ..l }
}

fn or(a: Dnf, b: Dnf) -> Option<Dnf> {
    if is_true(&a) || is_true(&b) {
        return Some(vec![vec![]]);
    }
    let mut d = a;
    for t in b {
        if !d.contains(&t) {
            d.push(t);
        }
    }
    let d = simplify_terms(d, negated);
    size_ok(&d).then_some(d)
}

pub fn and_dnf(a: &Dnf, b: &Dnf) -> Option<Dnf> {
    and(a, b)
}

fn and(a: &Dnf, b: &Dnf) -> Option<Dnf> {
    let mut d: Dnf = Vec::new();
    for x in a {
        for y in b {
            let mut t = x.clone();
            for l in y {
                if !t.contains(l) {
                    t.push(*l);
                }
            }
            // Drop contradictory terms (a literal together with its negation).
            if t.iter().any(|l| t.contains(&negated(*l))) {
                continue;
            }
            if !d.contains(&t) {
                d.push(t);
            }
            if d.len() > MAX_TERMS * MAX_TERMS {
                return None;
            }
        }
    }
    let d = simplify_terms(d, negated);
    size_ok(&d).then_some(d)
}

pub fn negate(d: &Dnf) -> Option<Dnf> {
    // ¬(T1 ∨ T2 ∨ …) = ¬T1 ∧ ¬T2 ∧ …, where ¬T is the OR of its negated literals.
    let mut acc: Dnf = vec![vec![]];
    for t in d {
        let not_t: Dnf = t.iter().map(|l| vec![negated(*l)]).collect();
        acc = and(&acc, &not_t)?;
    }
    Some(acc)
}

pub struct Fuser<'g> {
    pub g: &'g mut Graph,
    memo: HashMap<V, V>,
    dnf_memo: HashMap<(V, bool), Option<Dnf>>,
    /// Min/max nodes to build as order statistics: their leaves and rank (`sortnet.rs`).
    order_stats: HashMap<V, (Vec<V>, usize)>,
}

impl<'g> Fuser<'g> {
    pub fn new(g: &'g mut Graph) -> Self {
        Fuser { g, memo: HashMap::new(), dnf_memo: HashMap::new(), order_stats: HashMap::new() }
    }

    /// A single literal, folding constants.
    fn lit(&mut self, op: CmpOp, a: V, b: V) -> Dnf {
        let v = self.g.cmp(op, a, b);
        match self.g.op(v).clone() {
            Op::Const(k) => {
                if k != 0 {
                    vec![vec![]]
                } else {
                    vec![]
                }
            }
            Op::Cmp(op, a, b) => vec![vec![Lit { op, a, b }]],
            // cmp() can simplify `bool != 0` to the bool itself.
            _ => vec![vec![Lit { op: CmpOp::Ne, a: v, b: self.g.konst(0) }]],
        }
    }

    /// DNF of a boolean node (negated if `neg`), with leaves rebuilt. `None` if too large.
    pub fn dnf(&mut self, v: V, neg: bool) -> Option<Dnf> {
        if let Some(d) = self.dnf_memo.get(&(v, neg)) {
            return d.clone();
        }
        let is_bool = |g: &Graph, x: V| g.is_bool(x);
        let d = match self.g.op(v).clone() {
            Op::Const(k) => Some(if (k != 0) != neg { vec![vec![]] } else { vec![] }),
            // `b != 0` / `b == 0` on a boolean is `b` / `not b`.
            Op::Cmp(op @ (CmpOp::Ne | CmpOp::Eq), x, z) if self.g.as_const(z) == Some(0) && is_bool(self.g, x) => {
                self.dnf(x, neg ^ (op == CmpOp::Eq))
            }
            Op::Cmp(op, a, b) => {
                let (a, b) = (self.rebuild(a), self.rebuild(b));
                Some(self.lit(if neg { op.negate() } else { op }, a, b))
            }
            Op::Ar(op @ (ArOp::And | ArOp::Or | ArOp::Xor), x, y) if is_bool(self.g, x) && is_bool(self.g, y) => {
                match (op, neg) {
                    (ArOp::And, false) | (ArOp::Or, true) => and(&self.dnf(x, neg)?, &self.dnf(y, neg)?),
                    (ArOp::Or, false) | (ArOp::And, true) => or(self.dnf(x, neg)?, self.dnf(y, neg)?),
                    // x ^ y = (x ∧ ¬y) ∨ (¬x ∧ y);  ¬(x ^ y) = (x ∧ y) ∨ (¬x ∧ ¬y)
                    _ => {
                        let (px, nx) = (self.dnf(x, false)?, self.dnf(x, true)?);
                        let (py, ny) = (self.dnf(y, false)?, self.dnf(y, true)?);
                        if neg {
                            or(and(&px, &py)?, and(&nx, &ny)?)
                        } else {
                            or(and(&px, &ny)?, and(&nx, &py)?)
                        }
                    }
                }
            }
            // With t/f complementary: (t ∧ a) ∨ (f ∧ b), and ¬ is (t ∧ ¬a) ∨ (f ∧ ¬b).
            Op::Mux { t, f, a, b } if is_bool(self.g, a) && is_bool(self.g, b) => {
                let (dt, df) = (self.dnf(t, false)?, self.dnf(f, false)?);
                let (da, db) = (self.dnf(a, neg)?, self.dnf(b, neg)?);
                or(and(&dt, &da)?, and(&df, &db)?)
            }
            Op::Dec(arms) if arms.len() == 1 && arms[0].1 == 1 => {
                let d = arms[0].0.clone();
                if neg {
                    negate(&d)
                } else {
                    Some(d)
                }
            }
            _ => {
                let r = self.rebuild(v);
                let z = self.g.konst(0);
                Some(self.lit(if neg { CmpOp::Eq } else { CmpOp::Ne }, r, z))
            }
        };
        self.dnf_memo.insert((v, neg), d.clone());
        d
    }

    /// The node `v` with boolean subexpressions fused into deciders.
    pub fn rebuild(&mut self, v: V) -> V {
        if let Some(&r) = self.memo.get(&v) {
            return r;
        }
        // A tree of min/max that is an order statistic: selector combinators.
        if let Some(r) = self.order_stat(v) {
            self.memo.insert(v, r);
            return r;
        }
        let hint = self.g.iv(v);
        let r = match self.g.op(v).clone() {
            Op::Const(_) | Op::Src(_) | Op::Dec(_) | Op::BConst(_) | Op::Each(_) | Op::SigK(_) => v,
            Op::Bun(terms) => {
                let terms = terms.into_iter().map(|t| self.rebuild_term(t)).collect();
                let terms = self.combine_writes(terms);
                let terms = self.table_lookups(terms);
                self.g.bun(terms)
            }
            Op::BMux { .. } => {
                let mut arms = Vec::new();
                self.barms(v, vec![vec![]], &mut arms);
                self.g.bdec(merge_arms(arms))
            }
            Op::BDec(arms) => {
                let arms = arms.into_iter().map(|(d, x)| (self.rebuild_dnf(&d), self.rebuild(x))).collect();
                self.g.bdec(arms)
            }
            Op::BSelect(b, max, index) => {
                let b = self.rebuild(b);
                self.g.brank(b, max, index)
            }
            Op::BSelectAt(b, max, ix) => {
                let (b, ix) = (self.rebuild(b), self.rebuild(ix));
                self.g.intern_op(Op::BSelectAt(b, max, ix))
            }
            Op::BDot(a, b) => {
                let (a, b) = (self.rebuild(a), self.rebuild(b));
                self.g.bdot(a, b)
            }
            Op::BSel(b, mode, nonce) => {
                let b = self.rebuild(b);
                self.g.intern_op(Op::BSel(b, mode, nonce))
            }
            Op::SigOf(x) => {
                let x = self.rebuild(x);
                self.g.sigval(x)
            }
            Op::AGet(b, ix) => {
                let (b, ix) = (self.rebuild(b), self.rebuild(ix));
                self.g.aget_ix(b, ix)
            }
            Op::BGet(b, sig) => {
                let b = self.rebuild(b);
                self.g.bget(b, sig)
            }
            Op::BTotal(b) => {
                let b = self.rebuild(b);
                self.g.btotal(b)
            }
            Op::BCount(b) => {
                let b = self.rebuild(b);
                self.g.bcount(b)
            }
            Op::Sel(_) if self.picked_read(v).is_some() => self.picked_read(v).unwrap(),
            Op::Sel(arms) => {
                let arms = arms.into_iter().map(|(c, x)| (self.cond_node(c), self.rebuild(x))).collect();
                self.g.sel(arms)
            }
            Op::Ar(op @ (ArOp::And | ArOp::Or | ArOp::Xor), x, y) if self.g.is_bool(x) && self.g.is_bool(y) => {
                match self.dnf(v, false) {
                    Some(d) => self.g.dec(vec![(d, 1)], hint),
                    None => {
                        let (x, y) = (self.rebuild(x), self.rebuild(y));
                        self.g.ar(op, x, y)
                    }
                }
            }
            Op::Ar(ArOp::Add, x, y) => match self.count_sum(v) {
                Some(r) => r,
                None => {
                    let (x, y) = (self.rebuild(x), self.rebuild(y));
                    self.g.ar(ArOp::Add, x, y)
                }
            },
            Op::Ar(op, x, y) => {
                let (x, y) = (self.rebuild(x), self.rebuild(y));
                self.g.ar(op, x, y)
            }
            Op::Cmp(op, a, b) => {
                let (a, b) = (self.rebuild(a), self.rebuild(b));
                self.g.cmp(op, a, b)
            }
            Op::Mux { .. } if self.argmax_chain(v).is_some() => {
                let (steps, top0, best0) = self.argmax_chain(v).unwrap();
                self.argmax(steps, top0, best0)
            }
            Op::Mux { t, f, a, b } => {
                let consts = (self.g.as_const(a), self.g.as_const(b));
                let fused = match consts {
                    (Some(ka), Some(kb)) => match (self.dnf(t, false), self.dnf(f, false)) {
                        (Some(dt), Some(df)) => Some(self.g.dec(vec![(dt, ka), (df, kb)], hint)),
                        _ => None,
                    },
                    _ if self.g.is_bool(a) && self.g.is_bool(b) => self.dnf(v, false).map(|d| self.g.dec(vec![(d, 1)], hint)),
                    _ => None,
                };
                match fused {
                    Some(r) => r,
                    None => {
                        let (t, f) = (self.cond_node(t), self.cond_node(f));
                        let (a, b) = (self.rebuild(a), self.rebuild(b));
                        self.g.mux_tf(t, f, a, b)
                    }
                }
            }
        };
        // A rebuilt bundle keeps the elements' bounds the original had (array maps, writes).
        if self.g.is_bundle(r) {
            self.g.narrow(r, hint);
        }
        self.memo.insert(v, r);
        r
    }

    fn rebuild_term(&mut self, t: BTerm) -> BTerm {
        match t {
            BTerm::Map(op, b, k) => BTerm::Map(op, self.rebuild(b), self.rebuild(k)),
            BTerm::RMap(op, k, b) => BTerm::RMap(op, self.rebuild(k), self.rebuild(b)),
            BTerm::Zip(op, a, b) => BTerm::Zip(op, self.rebuild(a), self.rebuild(b)),
            BTerm::One(s, x) => {
                // The combinator that computes `x` can write the bundle's signal itself.
                let x = self.rebuild(x);
                match self.g.op(x).clone() {
                    Op::Ar(op, a, b) => BTerm::Ar(op, a, b, s),
                    _ => match self.const_arms(x, &[s]) {
                        Some(t) => t,
                        None => BTerm::One(s, x),
                    },
                }
            }
            BTerm::Ar(op, a, b, s) => BTerm::Ar(op, self.rebuild(a), self.rebuild(b), s),
            BTerm::Dec(arms) => BTerm::Dec(arms.into_iter().map(|(d, k)| (self.rebuild_dnf(&d), k)).collect()),
            BTerm::Set(b, s, x) => BTerm::Set(self.rebuild(b), s, self.rebuild(x)),
            BTerm::Filter(b, d, out) => {
                let mut op = |o: BOp| match o {
                    BOp::Each => BOp::Each,
                    BOp::Val(v) => BOp::Val(self.rebuild(v)),
                };
                let d = d.into_iter().map(|t| t.into_iter().map(|l| BLit { op: l.op, a: op(l.a), b: op(l.b) }).collect()).collect();
                BTerm::Filter(self.rebuild(b), d, out)
            }
            BTerm::DFilter(d, b, conds, out) => BTerm::DFilter(self.rebuild(d), self.rebuild(b), conds, out),
            BTerm::K(vals) => BTerm::K(vals),
            BTerm::Shift(s, x, c) => BTerm::Shift(s, self.rebuild(x), c),
            BTerm::Hot(t, ix, c) => {
                let t = self.rebuild(t);
                let ix = self.shared_hot_index(ix);
                BTerm::Hot(t, ix, c)
            }
            BTerm::HotEq(t, x, c) => BTerm::HotEq(self.rebuild(t), self.rebuild(x), c),
            BTerm::Fold(b, op, c, s) => BTerm::Fold(self.rebuild(b), op, c, s),
        }
    }

    /// The arms of a tree of bundle selects under `guard`: nested selects become arms whose
    /// guards are the conditions along their path (a priority mux, one stage deep). Returns
    /// whether every select below became arms (none left as a stage of its own).
    fn barms(&mut self, v: V, guard: Dnf, arms: &mut Vec<(Dnf, V)>) -> bool {
        if let Op::BMux { t, f, a, b } = *self.g.op(v) {
            let dt = self.dnf(t, false).unwrap_or_else(|| self.node_lit(t));
            let df = self.dnf(f, false).unwrap_or_else(|| self.node_lit(f));
            // Deeper selects only while the guards stay small enough for one decider.
            if arms.len() < MAX_ARMS {
                if let (Some(gt), Some(gf)) = (and(&guard, &dt), and(&guard, &df)) {
                    let n = arms.len();
                    if self.barms(a, gt, arms) & self.barms(b, gf, arms) {
                        return true;
                    }
                    // A select below didn't fit under these guards: test this condition as
                    // one node instead (`c != 0`, its complement `c == 0`), so `if big: (if
                    // q: xs[i] = k)` is arms of one stage (merged by value), not two stages.
                    let c = self.cond_node(t);
                    let z = self.g.konst(0);
                    let (nt, nf) = (self.lit(CmpOp::Ne, c, z), self.lit(CmpOp::Eq, c, z));
                    if nt == dt && nf == df {
                        return false;
                    }
                    let mut alt = arms[..n].to_vec();
                    if let (Some(gt), Some(gf)) = (and(&guard, &nt), and(&guard, &nf)) {
                        if self.barms(a, gt, &mut alt) & self.barms(b, gf, &mut alt) {
                            *arms = alt;
                            return true;
                        }
                    }
                    return false;
                }
            }
            let x = self.rebuild(v);
            arms.push((guard, x));
            return false;
        }
        let x = self.rebuild(v);
        arms.push((guard, x));
        true
    }

    /// `v != 0` as a condition list, with `v` as a single decider where possible.
    fn node_lit(&mut self, v: V) -> Dnf {
        let n = self.cond_node(v);
        let z = self.g.konst(0);
        self.lit(CmpOp::Ne, n, z)
    }

    fn rebuild_dnf(&mut self, d: &Dnf) -> Dnf {
        d.iter().map(|t| t.iter().map(|l| Lit { op: l.op, a: self.rebuild(l.a), b: self.rebuild(l.b) }).collect()).collect()
    }

    /// A boolean node as a single decider where possible.
    fn cond_node(&mut self, t: V) -> V {
        match self.dnf(t, false) {
            Some(d) => self.g.dec(vec![(d, 1)], Iv::BOOL),
            None => self.rebuild(t),
        }
    }

    pub fn cond(&mut self, v: V) -> CondPlan {
        let pos = self.dnf(v, false);
        let neg = self.dnf(v, true);
        let node = self.cond_node(v);
        CondPlan { node, pos, neg }
    }
}

/// Arms of a bundle select with the same bundle become one (guards OR'd; they never hold
/// together): one decider instead of several, e.g. the "unchanged" arms of nested `if`s.
fn merge_arms(arms: Vec<(Dnf, V)>) -> Vec<(Dnf, V)> {
    let mut out: Vec<(Dnf, V)> = Vec::new();
    for (d, x) in arms {
        let same = out.iter().position(|(_, y)| *y == x);
        match same.and_then(|i| or(out[i].0.clone(), d.clone()).map(|m| (i, m))) {
            Some((i, m)) => out[i].0 = m,
            None => out.push((d, x)),
        }
    }
    out
}

/// Nodes a set of loads needs computed: load values and condition operands.
pub fn load_operands(loads: &[Load]) -> Vec<V> {
    let mut out = Vec::new();
    for l in loads {
        out.extend(dnf_operands(&l.guard));
        if let LoadVal::Node(v) = l.val {
            out.push(v);
        }
    }
    out
}

/// Depth at which loads (or a condition list) are ready: their operands' depth.
pub fn ready_depth(depths: &[u32], nodes: impl IntoIterator<Item = V>) -> u32 {
    nodes.into_iter().map(|v| depths[v as usize]).max().unwrap_or(0)
}
