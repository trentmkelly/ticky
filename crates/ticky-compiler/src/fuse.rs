//! Fusion, run after lowering:
//!
//! * Boolean logic (comparisons combined with `and`/`or`/`not`, selects between constants)
//!   becomes multi-condition deciders: a decider evaluates an OR of AND-terms in one tick.
//! * A register update becomes a set of *guarded loads*: `x = a if c else x` loads `a` when
//!   `c` holds and otherwise keeps `x`, with no select stage at all.
//! * Branch and wait conditions keep their condition lists so they can be folded straight
//!   into the deciders that commit a step or choose the next one.

use std::collections::HashMap;

use ticky_factorio::{ArOp, CmpOp};

use crate::ir::{dnf_operands, BLit, BOp, BTerm, Dnf, Graph, Iv, Lit, Op, V};

/// Most guarded loads one register update is split into.
const MAX_LOADS: usize = 8;

/// Upper bounds on a fused condition, to keep deciders reasonable.
const MAX_TERMS: usize = 12;
const MAX_LITS: usize = 32;

#[derive(Clone, Debug)]
pub enum LoadVal {
    Const(i32),
    Node(V),
}

/// Load `val` into a register when `guard` holds at commit time. `guard == [[]]` is
/// unconditional. A `Const(0)` load writes nothing but still stops the register holding.
///
/// A *direct* load is a constant whose guard is checked by the load decider itself, on the
/// commit tick. Other guarded loads first compute an enable pulse one tick earlier.
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
            if d.len() > MAX_TERMS {
                return None;
            }
        }
    }
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
}

impl<'g> Fuser<'g> {
    pub fn new(g: &'g mut Graph) -> Self {
        Fuser { g, memo: HashMap::new(), dnf_memo: HashMap::new() }
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
        let hint = self.g.iv(v);
        let r = match self.g.op(v).clone() {
            Op::Const(_) | Op::Src(_) | Op::Dec(_) | Op::BConst(_) | Op::Each | Op::SigK(_) => v,
            Op::Bun(terms) => {
                let terms = terms.into_iter().map(|t| self.rebuild_term(t)).collect();
                self.g.bun(terms)
            }
            Op::BMux { t, f, a, b } => {
                let (t, f) = (self.cond_node(t), self.cond_node(f));
                let (a, b) = (self.rebuild(a), self.rebuild(b));
                self.g.bmux_tf(t, f, a, b)
            }
            Op::BSelect(b, max, index) => {
                let b = self.rebuild(b);
                self.g.brank(b, max, index)
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
            Op::Ar(op, x, y) => {
                let (x, y) = (self.rebuild(x), self.rebuild(y));
                self.g.ar(op, x, y)
            }
            Op::Cmp(op, a, b) => {
                let (a, b) = (self.rebuild(a), self.rebuild(b));
                self.g.cmp(op, a, b)
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
        self.memo.insert(v, r);
        r
    }

    fn rebuild_term(&mut self, t: BTerm) -> BTerm {
        match t {
            BTerm::Map(op, b, k) => BTerm::Map(op, self.rebuild(b), self.rebuild(k)),
            BTerm::RMap(op, k, b) => BTerm::RMap(op, self.rebuild(k), self.rebuild(b)),
            BTerm::Zip(op, a, b) => BTerm::Zip(op, self.rebuild(a), self.rebuild(b)),
            BTerm::One(s, x) => BTerm::One(s, self.rebuild(x)),
            BTerm::Pick(b, s, m) => BTerm::Pick(self.rebuild(b), s, m),
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
            BTerm::Hot(t, ix, c) => BTerm::Hot(self.rebuild(t), self.rebuild(ix), c),
            BTerm::Fold(b, op, c, s) => BTerm::Fold(self.rebuild(b), op, c, s),
        }
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

    /// Guarded loads that set a register to `next`; `own` is the register's own value (for
    /// paths that keep it). `None` if the register never changes.
    pub fn plan(&mut self, next: V, own: Option<V>) -> Option<Vec<Load>> {
        if Some(next) == own {
            return None;
        }
        let mut loads = Vec::new();
        self.split(next, vec![vec![]], own, &mut loads);
        Some(loads)
    }

    fn split(&mut self, v: V, guard: Dnf, own: Option<V>, loads: &mut Vec<Load>) {
        if Some(v) == own {
            return; // this path keeps the current value
        }
        if guard.is_empty() {
            return; // unreachable path
        }
        // Splitting a select only pays when a path keeps the old value or loads a constant
        // (otherwise it just multiplies loads), and the number of loads stays small.
        let worth = |this: &Self, x: V| Some(x) == own || this.g.as_const(x).is_some() || this.mentions(x, own);
        if let Some((t, f, a, b)) = self.g.as_mux(v) {
            // The top-level split is cheap (two loads) and saves the select stage.
            let top = is_true(&guard);
            let useful = (top || worth(self, a) || worth(self, b)) && loads.len() < MAX_LOADS;
            if let (true, Some(dt), Some(df)) = (useful, self.dnf(t, false), self.dnf(f, false)) {
                if let (Some(gt), Some(gf)) = (and(&guard, &dt), and(&guard, &df)) {
                    self.split(a, gt, own, loads);
                    self.split(b, gf, own, loads);
                    return;
                }
            }
        }
        let val = match self.g.as_const(v) {
            Some(k) => LoadVal::Const(k),
            None => {
                // A bool-valued node can itself split into constant loads: 1 when it holds,
                // 0 (stop holding) otherwise.
                if self.g.is_bool(v) {
                    if let (Some(p), Some(n)) = (self.dnf(v, false), self.dnf(v, true)) {
                        if let (Some(gp), Some(gn)) = (and(&guard, &p), and(&guard, &n)) {
                            if !gp.is_empty() {
                                loads.push(Load { guard: gp, val: LoadVal::Const(1), direct: false });
                            }
                            if !gn.is_empty() {
                                loads.push(Load { guard: gn, val: LoadVal::Const(0), direct: false });
                            }
                            return;
                        }
                    }
                }
                // Fusion can fold a value to a constant (e.g. an impossible condition).
                let r = self.rebuild(v);
                match self.g.as_const(r) {
                    Some(k) => LoadVal::Const(k),
                    None => LoadVal::Node(r),
                }
            }
        };
        loads.push(Load { guard, val, direct: false });
    }

    /// Whether `x` is a select tree with `own` (the old value) or a constant among its leaves.
    fn mentions(&self, x: V, own: Option<V>) -> bool {
        match self.g.as_mux(x) {
            Some((_, _, a, b)) => [a, b].iter().any(|y| Some(*y) == own || self.g.as_const(*y).is_some() || self.mentions(*y, own)),
            None => false,
        }
    }

    /// Plans a writer's update of a register. `None` if it never changes it.
    pub fn writer_plan(&mut self, next: V, own: Option<V>) -> Option<WriterPlan> {
        let mut loads = self.plan(next, own)?;
        // Constant loads under a condition can check it themselves, if the "none of them
        // fires" condition (needed by the hold decider) stays small.
        let mut union: Option<Dnf> = Some(vec![]);
        let mut any = false;
        for l in &loads {
            if matches!(l.val, LoadVal::Const(_)) && !is_true(&l.guard) {
                any = true;
                union = union.and_then(|u| or(u, l.guard.clone()));
            }
        }
        let keep = if any { union.as_ref().and_then(negate) } else { None };
        if keep.is_some() {
            for l in &mut loads {
                l.direct = matches!(l.val, LoadVal::Const(_)) && !is_true(&l.guard);
            }
        }
        Some(WriterPlan { loads, keep })
    }
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
