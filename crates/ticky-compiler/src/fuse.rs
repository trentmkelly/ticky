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

/// Most arms a tree of bundle selects is flattened into.
const MAX_ARMS: usize = 8;

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
                let terms = self.combine_writes(terms);
                let terms = self.table_lookups(terms);
                self.g.bun(terms)
            }
            Op::BMux { .. } => {
                let mut arms = Vec::new();
                self.barms(v, vec![vec![]], &mut arms);
                self.g.bdec(arms)
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
            BTerm::Hot(t, ix, c) => BTerm::Hot(self.rebuild(t), self.rebuild(ix), c),
            BTerm::Fold(b, op, c, s) => BTerm::Fold(self.rebuild(b), op, c, s),
        }
    }

    /// A running maximum that remembers which candidate won (`best, top = B0, T0`, then
    /// `if s_i > top: best, top = K_i, s_i` for each candidate in turn), seen from the final
    /// `best`: the candidates `(s_i, K_i)` in order, `T0` and `B0`. Strict `>`, so the
    /// earliest of equal maxima wins; three candidates at least; `T0 ≥ 0`.
    fn argmax_chain(&self, v: V) -> Option<(Vec<(V, i32)>, i32, i32)> {
        let g = &self.g;
        // `s > top`, either way round: (s, top).
        let gt = |c: V| match *g.op(c) {
            Op::Cmp(CmpOp::Gt, s, t) => Some((s, t)),
            Op::Cmp(CmpOp::Lt, t, s) => Some((s, t)),
            _ => None,
        };
        let mut steps = Vec::new();
        let mut best = v;
        // The `top` the current step compares with must be the previous step's update.
        let mut want_top: Option<(V, V, V)> = None; // (top node, its step's condition, its s)
        loop {
            let (c, k, prev) = match *g.op(best) {
                Op::Mux { t, a, b, .. } => match g.as_const(a) {
                    Some(k) => (t, k, Some(b)),
                    None => return None,
                },
                // `best = 1 if s > top else 0`, simplified to the comparison.
                Op::Cmp(..) => (best, 1, None),
                _ => return None,
            };
            let (s, top) = gt(c)?;
            if let Some((tn, tc, ts)) = want_top {
                match *g.op(tn) {
                    Op::Mux { t, a, b, .. } if t == tc && a == ts && b == top => {}
                    _ => return None,
                }
            }
            steps.push((s, k));
            let prev_best = match prev {
                Some(p) => p,
                None => {
                    // The first step's `best` was folded away: B0 = 0.
                    let t0 = g.as_const(top)?;
                    return (steps.len() >= 3 && t0 >= 0).then(|| {
                        steps.reverse();
                        (steps, t0, 0)
                    });
                }
            };
            if let (Some(b0), Some(t0)) = (g.as_const(prev_best), g.as_const(top)) {
                return (steps.len() >= 3 && t0 >= 0).then(|| {
                    steps.reverse();
                    (steps, t0, b0)
                });
            }
            // The previous `top` is `s_prev if c_prev else top_prev`: checked at the next step.
            let Op::Mux { t: pc, .. } = *g.op(top) else { return None };
            let ps = gt(pc)?.0;
            want_top = Some((top, pc, ps));
            best = prev_best;
        }
    }

    /// [`argmax_chain`](Self::argmax_chain) with a selector combinator: the candidates'
    /// scores on signals ranked in candidate order (so ties go to the earliest, as with
    /// `>`), those above `T0` kept, the largest selected, and its `K` read from a table.
    fn argmax(&mut self, steps: Vec<(V, i32)>, top0: i32, best0: i32) -> V {
        let t = ticky_factorio::SignalTable::base();
        let mut pool = t.internal_pool();
        pool.sort_by_key(|s| t.rank(*s));
        let sigs: Vec<_> = pool.into_iter().take(steps.len()).collect();
        let terms: Vec<BTerm> = steps.iter().zip(&sigs).map(|((s, _), sig)| {
            let x = self.rebuild(*s);
            BTerm::One(*sig, x)
        }).collect();
        let terms = terms.into_iter().map(|t| self.rebuild_term(t)).collect();
        let scores = self.g.bun(terms);
        let k0 = self.g.konst(top0);
        let above = self.g.bun(vec![BTerm::Filter(scores, vec![vec![BLit { op: CmpOp::Gt, a: BOp::Each, b: BOp::Val(k0) }]], crate::ir::FOut::Copy)]);
        let top = self.g.brank(above, true, 0);
        // K_i - B0 on each candidate's signal (a constant combinator can't hold 0: those
        // candidates add nothing, which is right).
        let table = self.g.bconst(steps.iter().zip(&sigs).map(|((_, k), sig)| (*sig, k.wrapping_sub(best0))));
        let z = self.g.konst(0);
        let won = self.g.bun(vec![BTerm::DFilter(table, top, vec![vec![BLit { op: CmpOp::Ne, a: BOp::Each, b: BOp::Val(z) }]], crate::ir::FOut::Copy)]);
        let k = self.g.btotal(won);
        let b0 = self.g.konst(best0);
        self.g.ar(ArOp::Add, k, b0)
    }

    /// The leaves of a tree of `+` (original nodes), at most `limit` of them.
    fn add_leaves(&self, v: V, out: &mut Vec<V>, limit: usize) -> bool {
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
    fn slot_test(&self, v: V) -> Option<(V, ticky_factorio::Sig, i32)> {
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
    fn count_sum(&mut self, v: V) -> Option<V> {
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

    /// One-hot outputs picked by comparing one scalar with constants (`A if x == 1 else B if
    /// x == 2 else …`, a decider per arm) become a table lookup: a constant table of the
    /// arms' values and one decider passing the signal whose value equals `x` (a [`BTerm::Hot`],
    /// plus the index signal; the table is shared by equal lookups).
    fn table_lookups(&mut self, terms: Vec<BTerm>) -> Vec<BTerm> {
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

    /// A rebuilt condition value `x` (constants under conditions) written on signals `sigs`:
    /// a decider per arm outputting the constant on all of them.
    fn const_arms(&mut self, x: V, sigs: &[ticky_factorio::Sig]) -> Option<BTerm> {
        let arms = match self.g.op(x).clone() {
            Op::Dec(arms) => arms,
            Op::Cmp(op, a, b) if self.g.as_const(a).is_none() => vec![(vec![vec![Lit { op, a, b }]], 1)],
            _ => return None,
        };
        Some(BTerm::Dec(arms.into_iter().map(|(d, k)| (d, crate::ir::normalize(sigs.iter().map(|s| (*s, k))))).collect()))
    }

    /// Several signals set on one bundle (`b0` copied, then `x_i - b0[s_i]` on each `s_i`):
    /// one combinator takes the old values out (`b0 × (-1 on every s_i)`), and the signals that
    /// get the same value share a term (constants, a decider per condition, or a table of
    /// ones times the value). Also `ones × condition` as deciders.
    fn combine_writes(&mut self, terms: Vec<BTerm>) -> Vec<BTerm> {
        let mut out = Vec::new();
        // base → [(signal, value)]
        let mut sets: Vec<(V, Vec<(ticky_factorio::Sig, V)>)> = Vec::new();
        for t in terms {
            match t {
                BTerm::Set(b0, s, x) => match sets.iter_mut().find(|(b, _)| *b == b0) {
                    Some((_, v)) => v.push((s, x)),
                    None => sets.push((b0, vec![(s, x)])),
                },
                BTerm::Map(ArOp::Mul, ones, x) if self.g.as_bconst(ones).is_some_and(|b| b.iter().all(|(_, k)| *k == 1)) => {
                    let sigs: Vec<_> = self.g.as_bconst(ones).unwrap().iter().map(|(s, _)| *s).collect();
                    match self.const_arms(x, &sigs) {
                        Some(d) => out.push(d),
                        None => out.push(BTerm::Map(ArOp::Mul, ones, x)),
                    }
                }
                t => out.push(t),
            }
        }
        for (b0, writes) in sets {
            if writes.len() == 1 {
                let (s, x) = writes[0];
                out.push(BTerm::Set(b0, s, x));
                continue;
            }
            let neg = self.g.bconst(writes.iter().map(|(s, _)| (*s, -1)));
            out.push(BTerm::Zip(ArOp::Mul, b0, neg));
            let mut konst = Vec::new();
            let mut groups: Vec<(V, Vec<ticky_factorio::Sig>)> = Vec::new();
            for (s, x) in writes {
                match self.g.as_const(x) {
                    Some(k) => konst.push((s, k)),
                    None => match groups.iter_mut().find(|(v, _)| *v == x) {
                        Some((_, ss)) => ss.push(s),
                        None => groups.push((x, vec![s])),
                    },
                }
            }
            out.push(BTerm::K(crate::ir::normalize(konst)));
            for (x, sigs) in groups {
                if let Some(d) = self.const_arms(x, &sigs) {
                    out.push(d);
                } else if let ([s], Op::Ar(op, a, b)) = (sigs.as_slice(), self.g.op(x).clone()) {
                    out.push(BTerm::Ar(op, a, b, *s));
                } else if let [s] = sigs.as_slice() {
                    out.push(BTerm::One(*s, x));
                } else {
                    let ones = self.g.bconst(sigs.iter().map(|s| (*s, 1)));
                    out.push(BTerm::Map(ArOp::Mul, ones, x));
                }
            }
        }
        out
    }

    /// The arms of a tree of bundle selects under `guard`: nested selects become arms whose
    /// guards are the conditions along their path (a priority mux, one stage deep).
    fn barms(&mut self, v: V, guard: Dnf, arms: &mut Vec<(Dnf, V)>) {
        if let Op::BMux { t, f, a, b } = *self.g.op(v) {
            let dt = self.dnf(t, false).unwrap_or_else(|| self.node_lit(t));
            let df = self.dnf(f, false).unwrap_or_else(|| self.node_lit(f));
            // Deeper selects only while the guards stay small enough for one decider.
            if arms.len() < MAX_ARMS {
                if let (Some(gt), Some(gf)) = (and(&guard, &dt), and(&guard, &df)) {
                    self.barms(a, gt, arms);
                    self.barms(b, gf, arms);
                    return;
                }
            }
        }
        let x = self.rebuild(v);
        arms.push((guard, x));
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
        // A running maximum is cheaper as one selector than as loads per candidate.
        if self.argmax_chain(v).is_some() {
            let r = self.rebuild(v);
            loads.push(Load { guard, val: LoadVal::Node(r), direct: false });
            return;
        }
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
