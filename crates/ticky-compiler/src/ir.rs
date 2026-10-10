//! Word-level dataflow IR. Every node is one 32-bit value computed by (at most) one
//! combinator. Nodes are hash-consed and simplified on construction, and each carries a
//! conservative integer interval used for folding and for proving operands non-negative.

use std::collections::{BTreeMap, HashMap};

use ticky_factorio::{ArOp, CmpOp, Selector, Sig, SignalTable};

pub type V = u32;

/// A constant bundle: signals with nonzero values, sorted by signal.
pub type BVals = Vec<(Sig, i32)>;

/// A compile-time constant value.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Cv {
    Int(i32),
    Bun(BVals),
    /// A signal (`S("iron-plate")`), usable as a bundle key.
    Sig(Sig),
}

impl Cv {
    pub fn int(&self) -> Option<i32> {
        match self {
            Cv::Int(k) => Some(*k),
            _ => None,
        }
    }
}

/// Sorted, merged, without zeros.
pub fn normalize(vals: impl IntoIterator<Item = (Sig, i32)>) -> BVals {
    let mut m: BTreeMap<Sig, i32> = BTreeMap::new();
    for (s, v) in vals {
        let e = m.entry(s).or_insert(0);
        *e = e.wrapping_add(v);
    }
    m.into_iter().filter(|(_, v)| *v != 0).collect()
}

fn bval(b: &BVals, s: Sig) -> i32 {
    b.binary_search_by_key(&s, |(x, _)| *x).map(|i| b[i].1).unwrap_or(0)
}

/// Operand of a per-signal condition: the value of the current signal (`each`) or a scalar.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum BOp {
    Each,
    Val(V),
}

/// One per-signal decider condition: `a op b`. `a` is never a constant.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct BLit {
    pub op: CmpOp,
    pub a: BOp,
    pub b: BOp,
}

pub type BDnf = Vec<Vec<BLit>>;

/// What a filter outputs for each signal that passes.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub enum FOut {
    Copy,
    Const(i32),
}

/// One combinator writing (part of) a bundle; a bundle node's value is the sum of its terms.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum BTerm {
    /// `each(b) op k` for every signal present in bundle `b` (`k` scalar or constant).
    Map(ArOp, V, V),
    /// `k op each(b)` for every signal present in `b`.
    RMap(ArOp, V, V),
    /// `each(a) op each(b)` over the union of the two bundles' signals.
    Zip(ArOp, V, V),
    /// A single signal carrying a scalar's value.
    One(Sig, V),
    /// `x - b[s]` on signal `s`: next to a copy of `b`, sets `s` to `x` (one arithmetic
    /// combinator reading `x` on green and `b` on red).
    Set(V, Sig, V),
    /// The signals of `b` passing a per-signal condition, copied or set to a constant.
    Filter(V, BDnf, FOut),
    /// The signals of the domain `d` (first) where a per-signal condition on bundle `b`
    /// holds, counting signals missing from `b` as 0: `each` reads `b`, and the decider
    /// iterates over the signals of both. Copies `d`'s values. Constants only in conditions.
    DFilter(V, V, BDnf, FOut),
    /// Constant signals (a constant combinator on the bundle's wire).
    K(BVals),
    /// A scalar plus a constant, on one signal (`x + k → s`): index wires.
    Shift(Sig, V, i32),
    /// One-hot: the signals of the constant bundle `table` (red) whose value equals the index
    /// signal on bundle `ix` (green), each set to the constant.
    Hot(V, V, i32),
    /// `each(b) op k`, summed onto one signal.
    Fold(V, ArOp, i32, Sig),
    /// Scalar arithmetic `a op b` written straight onto signal `s` of the bundle (instead of
    /// computing it on the bus and copying it with `One`).
    Ar(ArOp, V, V, Sig),
    /// Constant signals under conditions: each arm's constants while its condition holds (a
    /// decider per arm). Made by fusion from conditions written into bundles.
    Dec(Vec<(Dnf, BVals)>),
}

/// Index of a block-level source (own state register or sampled input).
pub type SrcId = u32;

/// One decider condition: `a op b`. `a` is never a constant.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub struct Lit {
    pub op: CmpOp,
    pub a: V,
    pub b: V,
}

/// Disjunctive normal form: OR of AND-terms. `[]` is false, `[[]]` is true.
pub type Dnf = Vec<Vec<Lit>>;

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum Op {
    Const(i32),
    Src(SrcId),
    Ar(ArOp, V, V),
    Cmp(CmpOp, V, V),
    /// `(t ? a : 0) + (f ? b : 0)`, where `t` and `f` are complementary booleans.
    Mux { t: V, f: V, a: V, b: V },
    /// Sum of `k` over the arms whose condition holds: one decider per arm, all writing
    /// the same signal.
    Dec(Vec<(Dnf, i32)>),
    /// `Σ cond ? val : 0` over arms with mutually exclusive boolean conditions (runtime
    /// array indexing): one gate per arm, all writing the same signal.
    Sel(Vec<(V, V)>),
    /// A constant bundle.
    BConst(BVals),
    /// A bundle: the sum of its terms.
    Bun(Vec<BTerm>),
    /// Bundle select: `t ? a : b` with complementary boolean conditions.
    BMux { t: V, f: V, a: V, b: V },
    /// Bundle select with mutually exclusive guards: the bundle of the arm whose guard holds
    /// (nothing if none does). One decider per arm, evaluating its guard itself, so an
    /// `if`/`elif` chain of selects is one stage.
    BDec(Vec<(Dnf, V)>),
    /// The single signal of a bundle ranked `index` (0-based) from the largest (`true`) or
    /// the smallest value.
    BSelect(V, bool, u32),
    /// Scalar: one signal of a bundle.
    BGet(V, Sig),
    /// Scalar: the sum of a bundle's values.
    BTotal(V),
    /// Scalar: how many signals a bundle has.
    BCount(V),
    /// Scalar: the value in bundle `b` (first) of the signal whose value in `ix` equals the
    /// index signal's (array reads: `ix` is a position table plus the index).
    AGet(V, V),
    /// Placeholder for the value variable while lowering a bundle comprehension.
    Each,
    /// A signal constant (`S("iron-plate")`): used as a bundle key, never computed.
    SigK(Sig),
    /// A runtime `Signal` value: the one-hot bundle `x` (that signal with value 1, or no
    /// signal at all). Only for typing: consumers use `x` itself ([`Graph::unsig`]).
    SigOf(V),
    /// Like `BSelect`, with the rank read at runtime from bundle `ix` (just the index signal).
    BSelectAt(V, bool, V),
    /// Scalar: `Σ a[s] · b[s]` (with `b` one-hot: `a`'s value of that signal).
    BDot(V, V),
    /// A selector combinator mode applied to a bundle: stack sizes, rocket capacities,
    /// quality filter or transfer, a random pick (never `Select`/`Count`, which have their
    /// own nodes). The number tells random picks apart (each call is its own selector); 0
    /// for the other modes.
    BSel(V, Selector, u32),
}

impl Op {
    /// Whether the node's value is a bundle.
    pub fn is_bundle(&self, src_bun: &[bool]) -> bool {
        match self {
            Op::BConst(_) | Op::Bun(_) | Op::BMux { .. } | Op::BDec(_) | Op::BSelect(..) | Op::BSelectAt(..) | Op::BSel(..) => true,
            Op::Src(s) => src_bun.get(*s as usize).copied().unwrap_or(false),
            _ => false,
        }
    }
}

impl BTerm {
    pub fn operands(&self) -> Vec<V> {
        match self {
            BTerm::Map(_, a, b) | BTerm::RMap(_, a, b) | BTerm::Zip(_, a, b) => vec![*a, *b],
            BTerm::One(_, x) => vec![*x],
            BTerm::Set(b, _, x) => vec![*b, *x],
            BTerm::Filter(b, d, _) | BTerm::DFilter(_, b, d, _) => {
                let mut v = vec![*b];
                if let BTerm::DFilter(dom, ..) = self {
                    v.push(*dom);
                }
                for l in d.iter().flatten() {
                    for o in [l.a, l.b] {
                        if let BOp::Val(x) = o {
                            v.push(x);
                        }
                    }
                }
                v
            }
            BTerm::K(_) => vec![],
            BTerm::Shift(_, x, _) => vec![*x],
            BTerm::Ar(_, a, b, _) => vec![*a, *b],
            BTerm::Dec(arms) => arms.iter().flat_map(|(d, _)| dnf_operands(d)).collect(),
            BTerm::Hot(t, ix, _) => vec![*t, *ix],
            BTerm::Fold(b, ..) => vec![*b],
        }
    }
}

pub fn dnf_operands(d: &Dnf) -> impl Iterator<Item = V> + '_ {
    d.iter().flatten().flat_map(|l| [l.a, l.b])
}

/// Inclusive integer interval within the i32 range.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub struct Iv {
    pub lo: i64,
    pub hi: i64,
}

const MIN: i64 = i32::MIN as i64;
const MAX: i64 = i32::MAX as i64;

impl Iv {
    pub const FULL: Iv = Iv { lo: MIN, hi: MAX };
    pub const BOOL: Iv = Iv { lo: 0, hi: 1 };

    pub fn k(v: i32) -> Iv {
        Iv { lo: v as i64, hi: v as i64 }
    }

    /// Interval from i64 bounds; anything that could overflow i32 wraps, so becomes FULL.
    fn checked(lo: i64, hi: i64) -> Iv {
        if lo < MIN || hi > MAX {
            Iv::FULL
        } else {
            Iv { lo, hi }
        }
    }

    pub fn join(self, o: Iv) -> Iv {
        Iv { lo: self.lo.min(o.lo), hi: self.hi.max(o.hi) }
    }

    pub fn contains(self, o: Iv) -> bool {
        self.lo <= o.lo && o.hi <= self.hi
    }

    pub fn nonneg(self) -> bool {
        self.lo >= 0
    }

    pub fn is_bool(self) -> bool {
        self.lo >= 0 && self.hi <= 1
    }

    fn max_abs(self) -> i64 {
        self.lo.abs().max(self.hi.abs())
    }
}

fn bits_mask(hi: i64) -> i64 {
    let mut m = 0i64;
    while m < hi {
        m = m * 2 + 1;
    }
    m
}

fn interval(op: &Op, iv: impl Fn(V) -> Iv, konst: impl Fn(V) -> Option<i32>, src_iv: &[Iv]) -> Iv {
    match *op {
        Op::Const(k) => Iv::k(k),
        Op::Src(s) => src_iv[s as usize],
        Op::Cmp(..) => Iv::BOOL,
        Op::Mux { a, b, .. } => iv(a).join(iv(b)),
        Op::BConst(_) | Op::Bun(_) | Op::BMux { .. } | Op::BSelect(..) | Op::BGet(..) | Op::BTotal(_) | Op::AGet(..) | Op::Each | Op::SigK(_) => Iv::FULL,
        Op::SigOf(_) | Op::BSelectAt(..) | Op::BDot(..) | Op::BDec(_) | Op::BSel(..) => Iv::FULL,
        Op::BCount(_) => Iv { lo: 0, hi: MAX },
        Op::Sel(ref arms) => arms.iter().fold(Iv::k(0), |acc, (_, v)| acc.join(iv(*v))),
        Op::Dec(ref arms) => {
            // Any subset of arms may fire; bound the sum by the negative and positive parts.
            let lo: i64 = arms.iter().map(|(_, k)| (*k as i64).min(0)).sum();
            let hi: i64 = arms.iter().map(|(_, k)| (*k as i64).max(0)).sum();
            Iv::checked(lo, hi)
        }
        Op::Ar(op, a, b) => {
            let (x, y) = (iv(a), iv(b));
            match op {
                ArOp::Add => Iv::checked(x.lo + y.lo, x.hi + y.hi),
                ArOp::Sub => Iv::checked(x.lo - y.hi, x.hi - y.lo),
                ArOp::Mul => {
                    let p = [x.lo * y.lo, x.lo * y.hi, x.hi * y.lo, x.hi * y.hi];
                    let (lo, hi) = (*p.iter().min().unwrap(), *p.iter().max().unwrap());
                    // Products of i32 bounds fit in i64.
                    Iv::checked(lo, hi)
                }
                ArOp::Div => match konst(b) {
                    Some(0) => Iv::k(0),
                    Some(-1) if x.lo == MIN => Iv::FULL,
                    Some(k) => {
                        let (p, q) = (x.lo / k as i64, x.hi / k as i64);
                        Iv { lo: p.min(q), hi: p.max(q) }
                    }
                    None if x.nonneg() && y.nonneg() => Iv { lo: 0, hi: x.hi },
                    None => {
                        let m = x.max_abs().min(MAX);
                        Iv { lo: -m, hi: m }
                    }
                },
                ArOp::Mod => {
                    let m = match konst(b) {
                        Some(0) => return Iv::k(0),
                        Some(k) => (k as i64).abs() - 1,
                        None => (y.max_abs() - 1).max(0),
                    };
                    let m = m.min(x.max_abs());
                    if x.nonneg() {
                        Iv { lo: 0, hi: m }
                    } else if x.hi <= 0 {
                        Iv { lo: -m, hi: 0 }
                    } else {
                        Iv { lo: -m, hi: m }
                    }
                }
                ArOp::Shr => match konst(b) {
                    Some(k) => {
                        let k = (k as u32 & 31) as i64;
                        Iv { lo: x.lo >> k, hi: x.hi >> k }
                    }
                    None if x.nonneg() => Iv { lo: 0, hi: x.hi },
                    None => Iv { lo: x.lo.min(-1), hi: x.hi.max(0) },
                },
                ArOp::Shl => match konst(b) {
                    Some(k) => {
                        let k = (k as u32 & 31) as i64;
                        Iv::checked(x.lo << k, x.hi << k)
                    }
                    None => Iv::FULL,
                },
                ArOp::And => match (x.nonneg(), y.nonneg()) {
                    (true, true) => Iv { lo: 0, hi: x.hi.min(y.hi) },
                    (true, false) => Iv { lo: 0, hi: x.hi },
                    (false, true) => Iv { lo: 0, hi: y.hi },
                    _ => Iv::FULL,
                },
                ArOp::Or | ArOp::Xor if x.nonneg() && y.nonneg() => Iv { lo: 0, hi: bits_mask(x.hi.max(y.hi)) },
                ArOp::Or | ArOp::Xor | ArOp::Pow => Iv::FULL,
            }
        }
    }
}

#[derive(Default)]
pub struct Graph {
    pub nodes: Vec<Op>,
    ivs: Vec<Iv>,
    memo: HashMap<Op, V>,
    /// Interval assumed for each source.
    pub src_iv: Vec<Iv>,
    /// Which sources are bundles.
    pub src_bun: Vec<bool>,
    /// Which sources are runtime `Signal` values (one-hot bundles).
    pub src_sig: Vec<bool>,
    bun: Vec<bool>,
    /// Whether each node depends on the comprehension placeholder ([`Op::Each`]).
    each_dep: Vec<bool>,
    /// Runtime checks (`--checks`): a condition that is true when the check fails, where it
    /// is, and what it checks.
    pub checks: Vec<(V, ticky_syntax::Span, &'static str)>,
    /// Conditions under which the code being lowered runs (the branches of `if`s and of
    /// `x if c else y`, the right side of `and`/`or`): a check only fails where it runs.
    pub path: Vec<V>,
    /// How many bundle comprehensions are being lowered: inside one, `//` and `%` truncate.
    pub in_comp: u32,
    /// Random picks made so far (`Op::BSel` numbers).
    pub nonce: u32,
}

impl Graph {
    pub fn new(src_iv: Vec<Iv>) -> Self {
        Graph { src_iv, ..Default::default() }
    }

    pub fn op(&self, v: V) -> &Op {
        &self.nodes[v as usize]
    }

    pub fn iv(&self, v: V) -> Iv {
        self.ivs[v as usize]
    }

    pub fn as_const(&self, v: V) -> Option<i32> {
        match self.nodes[v as usize] {
            Op::Const(k) => Some(k),
            _ => None,
        }
    }

    pub fn is_bool(&self, v: V) -> bool {
        !self.bun[v as usize] && self.iv(v).is_bool()
    }

    pub fn is_bundle(&self, v: V) -> bool {
        self.bun[v as usize]
    }

    /// Whether `v` depends on a comprehension's value variable.
    pub fn uses_each(&self, v: V) -> bool {
        self.each_dep[v as usize]
    }

    pub fn as_bconst(&self, v: V) -> Option<&BVals> {
        match &self.nodes[v as usize] {
            Op::BConst(b) => Some(b),
            _ => None,
        }
    }

    /// A constant's value, if `v` is one.
    pub fn as_cv(&self, v: V) -> Option<Cv> {
        match &self.nodes[v as usize] {
            Op::Const(k) => Some(Cv::Int(*k)),
            Op::BConst(b) => Some(Cv::Bun(b.clone())),
            Op::SigK(s) => Some(Cv::Sig(*s)),
            _ => None,
        }
    }

    pub fn as_sig(&self, v: V) -> Option<Sig> {
        match self.nodes[v as usize] {
            Op::SigK(s) => Some(s),
            _ => None,
        }
    }

    pub fn sigk(&mut self, s: Sig) -> V {
        self.intern(Op::SigK(s))
    }

    /// Interns `op` as it is (for rebuilding nodes without simplification).
    pub fn intern_op(&mut self, op: Op) -> V {
        self.intern(op)
    }

    fn intern(&mut self, op: Op) -> V {
        self.intern_hint(op, Iv::FULL)
    }

    /// Interns with an extra known bound on the value (e.g. carried over from the node a
    /// rewrite replaces).
    fn intern_hint(&mut self, op: Op, hint: Iv) -> V {
        if let Some(&v) = self.memo.get(&op) {
            return v;
        }
        let iv = interval(&op, |v| self.ivs[v as usize], |v| self.as_const(v), &self.src_iv);
        let iv = Iv { lo: iv.lo.max(hint.lo), hi: iv.hi.min(hint.hi) };
        // An interval that pins a single value is a constant.
        if iv.lo == iv.hi && !matches!(op, Op::Const(_)) {
            return self.konst(iv.lo as i32);
        }
        let v = self.nodes.len() as V;
        self.bun.push(op.is_bundle(&self.src_bun));
        self.nodes.push(op.clone());
        self.ivs.push(iv);
        let dep = matches!(op, Op::Each) || self.operands(v).iter().any(|o| self.each_dep[*o as usize]);
        self.each_dep.push(dep);
        self.memo.insert(op, v);
        v
    }

    pub fn konst(&mut self, k: i32) -> V {
        self.intern(Op::Const(k))
    }

    pub fn src(&mut self, s: SrcId) -> V {
        self.intern(Op::Src(s))
    }

    pub fn ar(&mut self, op: ArOp, a: V, b: V) -> V {
        let (ka, kb) = (self.as_const(a), self.as_const(b));
        if let (Some(x), Some(y)) = (ka, kb) {
            return self.konst(op.apply(x, y));
        }
        // Constants go second for commutative operators.
        let (a, b, ka, kb) = if op.commutative() && ka.is_some() { (b, a, kb, ka) } else { (a, b, ka, kb) };
        let zero = self.konst(0);
        match (op, kb) {
            (ArOp::Add | ArOp::Sub | ArOp::Or | ArOp::Xor, Some(0)) => return a,
            (ArOp::Shl | ArOp::Shr, Some(k)) if k & 31 == 0 => return a,
            (ArOp::Mul | ArOp::Div | ArOp::Pow, Some(1)) => return a,
            (ArOp::Mul | ArOp::And, Some(0)) => return zero,
            (ArOp::Mod, Some(1 | -1)) => return zero,
            (ArOp::Pow, Some(0)) => return self.konst(1),
            (ArOp::And, Some(-1)) => return a,
            _ => {}
        }
        if ka == Some(0) && matches!(op, ArOp::Div | ArOp::Mod | ArOp::Shl | ArOp::Shr | ArOp::Mul) {
            return zero;
        }
        if a == b {
            match op {
                ArOp::Sub | ArOp::Xor => return zero,
                ArOp::And | ArOp::Or => return a,
                _ => {}
            }
        }
        if op == ArOp::And && kb == Some(1) && self.is_bool(a) {
            return a;
        }
        self.intern(Op::Ar(op, a, b))
    }

    pub fn cmp(&mut self, op: CmpOp, a: V, b: V) -> V {
        if let (Some(x), Some(y)) = (self.as_const(a), self.as_const(b)) {
            return self.konst(op.apply(x, y) as i32);
        }
        if a == b {
            return self.konst(matches!(op, CmpOp::Eq | CmpOp::Ge | CmpOp::Le) as i32);
        }
        // Decide from intervals where possible.
        let (x, y) = (self.iv(a), self.iv(b));
        let decided = match op {
            CmpOp::Lt if x.hi < y.lo => Some(true),
            CmpOp::Lt if x.lo >= y.hi => Some(false),
            CmpOp::Le if x.hi <= y.lo => Some(true),
            CmpOp::Le if x.lo > y.hi => Some(false),
            CmpOp::Gt if x.lo > y.hi => Some(true),
            CmpOp::Gt if x.hi <= y.lo => Some(false),
            CmpOp::Ge if x.lo >= y.hi => Some(true),
            CmpOp::Ge if x.hi < y.lo => Some(false),
            CmpOp::Eq | CmpOp::Ne if x.hi < y.lo || y.hi < x.lo => Some(op == CmpOp::Ne),
            _ => None,
        };
        if let Some(d) = decided {
            return self.konst(d as i32);
        }
        // A constant first operand is flipped to second (deciders need a signal first).
        if self.as_const(a).is_some() {
            return self.cmp(op.flip(), b, a);
        }
        // `x + k <op> c` → `x <op> c - k`, when neither side can wrap: saves a combinator.
        if let (Op::Ar(aop @ (ArOp::Add | ArOp::Sub), x, kv), Some(c)) = (self.op(a).clone(), self.as_const(b)) {
            if let Some(k) = self.as_const(kv) {
                let k = if aop == ArOp::Add { k as i64 } else { -(k as i64) };
                let xi = self.iv(x);
                let c2 = c as i64 - k;
                let no_wrap = xi.lo + k >= MIN && xi.hi + k <= MAX;
                if no_wrap && (MIN..=MAX).contains(&c2) {
                    let c2 = self.konst(c2 as i32);
                    return self.cmp(op, x, c2);
                }
            }
        }
        // `bool != 0` and `bool == 1` are the bool itself.
        if self.is_bool(a) && matches!((op, self.as_const(b)), (CmpOp::Ne, Some(0)) | (CmpOp::Eq, Some(1)) | (CmpOp::Gt, Some(0))) {
            return a;
        }
        self.intern(Op::Cmp(op, a, b))
    }

    /// Records a runtime check that fails when `fail` is true (with `--checks` only).
    pub fn check(&mut self, fail: V, span: ticky_syntax::Span, what: &'static str) {
        if !crate::checks_on() {
            return;
        }
        let mut f = self.truth(fail);
        for p in self.path.clone() {
            f = self.ar(ArOp::And, f, p);
        }
        if self.as_const(f) != Some(0) {
            self.checks.push((f, span, what));
        }
    }

    /// Runs `f` with `cond` (a 0/1 value) added to the path condition.
    pub fn under<T>(&mut self, cond: V, f: impl FnOnce(&mut Self) -> T) -> T {
        self.path.push(cond);
        let r = f(self);
        self.path.pop();
        r
    }

    /// Python truthiness as a 0/1 value (a bundle is true when it has any signal; a runtime
    /// signal when it is one, i.e. not "no signal").
    pub fn truth(&mut self, v: V) -> V {
        // A signal is true unless it's "no signal": the one-hot bundle is non-empty. (Signal
        // state and ports are already that bundle, so `unsig` leaves them as they are.)
        let v = if self.is_sigval(v) { self.unsig(v) } else { v };
        if self.is_bundle(v) {
            let n = self.bcount(v);
            let z = self.konst(0);
            return self.cmp(CmpOp::Ne, n, z);
        }
        if self.is_bool(v) {
            v
        } else {
            let z = self.konst(0);
            self.cmp(CmpOp::Ne, v, z)
        }
    }

    /// Logical not as a 0/1 value.
    pub fn not(&mut self, v: V) -> V {
        if let Op::Cmp(op, a, b) = *self.op(v) {
            return self.cmp(op.negate(), a, b);
        }
        let z = self.konst(0);
        self.cmp(CmpOp::Eq, v, z)
    }

    /// A mux from precomputed complementary conditions.
    pub fn mux_tf(&mut self, t: V, f: V, a: V, b: V) -> V {
        if a == b {
            return a;
        }
        if self.is_bundle(a) {
            return self.bmux_tf(t, f, a, b);
        }
        // Fusion can fold a condition to a constant.
        if let Some(k) = self.as_const(t) {
            return if k != 0 { a } else { b };
        }
        if let Some(k) = self.as_const(f) {
            return if k != 0 { b } else { a };
        }
        self.intern(Op::Mux { t, f, a, b })
    }

    /// A decider node; simplifies trivial cases. `hint` bounds its value.
    pub fn dec(&mut self, arms: Vec<(Dnf, i32)>, hint: Iv) -> V {
        let arms: Vec<(Dnf, i32)> = arms.into_iter().filter(|(d, k)| *k != 0 && !d.is_empty()).collect();
        match arms.as_slice() {
            [] => return self.konst(0),
            [(d, k)] if d.iter().any(|t| t.is_empty()) => return self.konst(*k),
            [(d, 1)] if d.len() == 1 && d[0].len() == 1 => {
                let l = d[0][0];
                return self.cmp(l.op, l.a, l.b);
            }
            _ => {}
        }
        self.intern_hint(Op::Dec(arms), hint)
    }

    /// `Σ cond ? val : 0`; conditions must be booleans that are never true together.
    pub fn sel(&mut self, arms: Vec<(V, V)>) -> V {
        let arms: Vec<(V, V)> = arms
            .into_iter()
            .filter(|(c, v)| self.as_const(*c) != Some(0) && self.as_const(*v) != Some(0))
            .collect();
        match arms.as_slice() {
            [] => self.konst(0),
            [(c, v)] if self.as_const(*c) == Some(1) => *v,
            [(c, v)] => {
                let z = self.konst(0);
                let f = self.not(*c);
                self.mux_tf(*c, f, *v, z)
            }
            _ => self.intern(Op::Sel(arms)),
        }
    }

    /// `a if c else b`, with `c` interpreted by truthiness.
    pub fn mux(&mut self, c: V, a: V, b: V) -> V {
        let t = self.truth(c);
        if let Some(k) = self.as_const(t) {
            return if k != 0 { a } else { b };
        }
        if a == b {
            return a;
        }
        // Signals (runtime, or different constants): select between one-hot bundles.
        let sig = |g: &Self, v: V| g.is_sigval(v) || g.as_sig(v).is_some();
        if sig(self, a) && sig(self, b) {
            let (x, y) = (self.unsig(a), self.unsig(b));
            let f = self.not(t);
            let m = self.bmux_tf(t, f, x, y);
            return self.sigval(m);
        }
        if self.is_bundle(a) {
            let f = self.not(t);
            return self.bmux_tf(t, f, a, b);
        }
        match (self.as_const(a), self.as_const(b)) {
            (Some(1), Some(0)) => return t,
            (Some(0), Some(1)) => return self.not(t),
            _ => {}
        }
        let f = self.not(t);
        self.intern(Op::Mux { t, f, a, b })
    }


    // ------------------------------------------------------------------ bundles

    pub fn bconst(&mut self, vals: impl IntoIterator<Item = (Sig, i32)>) -> V {
        let b = normalize(vals);
        self.intern(Op::BConst(b))
    }

    pub fn empty_bundle(&mut self) -> V {
        self.bconst([])
    }

    /// A constant as a node.
    pub fn cv(&mut self, c: &Cv) -> V {
        match c {
            Cv::Int(k) => self.konst(*k),
            Cv::Bun(b) => self.bconst(b.iter().copied()),
            Cv::Sig(s) => self.sigk(*s),
        }
    }

    pub fn each(&mut self) -> V {
        self.intern(Op::Each)
    }

    /// The constant value of a bundle term, when all its operands are constants.
    fn fold_term(&self, t: &BTerm) -> Option<BVals> {
        let k = |v: V| self.as_const(v);
        let b = |v: V| self.as_bconst(v);
        Some(match t {
            BTerm::Map(op, x, y) => {
                let (x, y) = (b(*x)?, k(*y)?);
                normalize(x.iter().map(|(s, v)| (*s, op.apply(*v, y))))
            }
            BTerm::RMap(op, x, y) => {
                let (x, y) = (k(*x)?, b(*y)?);
                normalize(y.iter().map(|(s, v)| (*s, op.apply(x, *v))))
            }
            BTerm::Zip(op, x, y) => {
                let (x, y) = (b(*x)?, b(*y)?);
                let mut sigs: Vec<Sig> = x.iter().chain(y.iter()).map(|(s, _)| *s).collect();
                sigs.sort();
                sigs.dedup();
                normalize(sigs.into_iter().map(|s| (s, op.apply(bval(x, s), bval(y, s)))))
            }
            BTerm::One(s, x) => normalize([(*s, k(*x)?)]),
            BTerm::Set(x, s, v) => normalize([(*s, k(*v)?.wrapping_sub(bval(b(*x)?, *s)))]),
            BTerm::Filter(x, d, out) => {
                let x = b(*x)?;
                let val = |o: BOp, cur: i32| -> Option<i32> {
                    match o {
                        BOp::Each => Some(cur),
                        BOp::Val(v) => k(v),
                    }
                };
                let mut res = Vec::new();
                for &(s, v) in x {
                    let mut any = false;
                    for term in d {
                        let mut all = true;
                        for l in term {
                            all &= l.op.apply(val(l.a, v)?, val(l.b, v)?);
                        }
                        any |= all;
                    }
                    if any {
                        res.push((s, match out {
                            FOut::Copy => v,
                            FOut::Const(c) => *c,
                        }));
                    }
                }
                normalize(res)
            }
            BTerm::DFilter(dom, x, d, out) => {
                let (dom, x) = (b(*dom)?, b(*x)?);
                let mut res = Vec::new();
                for &(s, dv) in dom {
                    let v = bval(x, s);
                    let lit = |o: BOp| -> Option<i32> {
                        match o {
                            BOp::Each => Some(v),
                            BOp::Val(c) => k(c),
                        }
                    };
                    let mut any = false;
                    for term in d {
                        let mut all = true;
                        for l in term {
                            all &= l.op.apply(lit(l.a)?, lit(l.b)?);
                        }
                        any |= all;
                    }
                    if any {
                        res.push((s, match out {
                            FOut::Copy => dv,
                            FOut::Const(c) => *c,
                        }));
                    }
                }
                normalize(res)
            }
            BTerm::K(vals) => vals.clone(),
            BTerm::Shift(s, x, c) => normalize([(*s, k(*x)?.wrapping_add(*c))]),
            // Made by fusion from non-constant nodes.
            BTerm::Ar(..) | BTerm::Dec(..) => return None,
            BTerm::Hot(t, ix, c) => {
                let (t, ix) = (b(*t)?, b(*ix)?);
                let i = bval(ix, SignalTable::base().index_signal());
                normalize(t.iter().filter(|(_, v)| *v == i).map(|(s, _)| (*s, *c)))
            }
            BTerm::Fold(x, op, c, s) => {
                let x = b(*x)?;
                normalize([(*s, x.iter().fold(0i32, |acc, (_, v)| acc.wrapping_add(op.apply(*v, *c))))])
            }
        })
    }

    /// A bundle made of terms; constant terms are folded together.
    pub fn bun(&mut self, terms: Vec<BTerm>) -> V {
        let mut konst: BVals = Vec::new();
        let mut rest = Vec::new();
        for t in terms {
            match self.fold_term(&t) {
                Some(vals) => konst.extend(vals),
                None => rest.push(t),
            }
        }
        let konst = normalize(konst);
        // A filter that never passes contributes nothing.
        rest.retain(|t| !matches!(t, BTerm::Filter(_, d, _) | BTerm::DFilter(_, _, d, _) if d.is_empty()));
        rest.retain(|t| !matches!(t, BTerm::Hot(_, _, 0) | BTerm::DFilter(_, _, _, FOut::Const(0)) | BTerm::Filter(_, _, FOut::Const(0))));
        if rest.is_empty() {
            return self.bconst(konst);
        }
        // Identities that need no combinator.
        if konst.is_empty() && rest.len() == 1 {
            if let Some(b) = self.identity(&rest[0]) {
                return b;
            }
        }
        // Sums of single-signal bundles stay single signals.
        if let [BTerm::Zip(op @ (ArOp::Add | ArOp::Sub), a, b)] = rest.as_slice() {
            if let (Some(pa), Some(pb)) = (self.singles(*a), self.singles(*b)) {
                let (op, a_parts) = (*op, pa);
                let mut m = self.collect(a_parts);
                for (s, p) in pb {
                    let y = match p {
                        Ok(v) => v,
                        Err(k) => self.konst(k),
                    };
                    let cur = m.get(&s).copied().unwrap_or_else(|| self.konst(0));
                    let v = self.ar(op, cur, y);
                    m.insert(s, v);
                }
                let mut terms: Vec<BTerm> = m.into_iter().map(|(s, v)| BTerm::One(s, v)).collect();
                terms.push(BTerm::K(konst));
                return self.bun(terms);
            }
        }
        // A filter of a filter is one filter (the inner one copies values unchanged).
        let rest: Vec<BTerm> = rest.into_iter().map(|t| self.merge_filter(t)).collect();
        if !konst.is_empty() {
            let mut rest = rest;
            rest.push(BTerm::K(konst));
            return self.intern(Op::Bun(rest));
        }
        self.intern(Op::Bun(rest))
    }

    /// The bundle a term passes through unchanged (`b + 0`, `b * 1`, `a + empty`, …).
    fn identity(&self, t: &BTerm) -> Option<V> {
        let empty = |v: V| self.as_bconst(v).is_some_and(|x| x.is_empty());
        match *t {
            BTerm::Map(ArOp::Add | ArOp::Sub | ArOp::Or | ArOp::Xor | ArOp::Shl | ArOp::Shr, b, k) if self.as_const(k) == Some(0) => Some(b),
            BTerm::Map(ArOp::Mul | ArOp::Div | ArOp::Pow, b, k) if self.as_const(k) == Some(1) => Some(b),
            BTerm::Zip(ArOp::Add | ArOp::Sub, a, b) if empty(b) => Some(a),
            BTerm::Zip(ArOp::Add, a, b) if empty(a) => Some(b),
            _ => None,
        }
    }

    fn merge_filter(&self, t: BTerm) -> BTerm {
        if let BTerm::Filter(b, d, out) = &t {
            if let Op::Bun(inner) = self.op(*b) {
                if let [BTerm::Filter(b2, d2, FOut::Copy)] = inner.as_slice() {
                    let mut both: BDnf = Vec::new();
                    for x in d2 {
                        for y in d {
                            both.push(x.iter().chain(y.iter()).copied().collect());
                        }
                    }
                    if both.len() <= 12 {
                        return BTerm::Filter(*b2, both, *out);
                    }
                }
            }
        }
        t
    }

    /// Scalar parts of a bundle built only from single signals and constants, if it is one.
    fn singles(&self, b: V) -> Option<Vec<(Sig, Result<V, i32>)>> {
        match self.op(b) {
            Op::BConst(vals) => Some(vals.iter().map(|(s, v)| (*s, Err(*v))).collect()),
            Op::Bun(terms) => {
                let mut out = Vec::new();
                for t in terms {
                    match t {
                        BTerm::One(s, x) => out.push((*s, Ok(*x))),
                        BTerm::K(vals) => out.extend(vals.iter().map(|(s, v)| (*s, Err(*v)))),
                        _ => return None,
                    }
                }
                Some(out)
            }
            _ => None,
        }
    }

    fn sum_parts(&mut self, parts: Vec<Result<V, i32>>) -> V {
        let mut acc = self.konst(0);
        for p in parts {
            let x = match p {
                Ok(v) => v,
                Err(k) => self.konst(k),
            };
            acc = self.ar(ArOp::Add, acc, x);
        }
        acc
    }

    pub fn bget(&mut self, b: V, s: Sig) -> V {
        if let Some(parts) = self.singles(b) {
            let mine = parts.into_iter().filter(|(x, _)| *x == s).map(|(_, p)| p).collect();
            return self.sum_parts(mine);
        }
        self.intern(Op::BGet(b, s))
    }

    pub fn btotal(&mut self, b: V) -> V {
        if let Some(parts) = self.singles(b) {
            return self.sum_parts(parts.into_iter().map(|(_, p)| p).collect());
        }
        self.intern(Op::BTotal(b))
    }

    pub fn bcount(&mut self, b: V) -> V {
        if let Some(vals) = self.as_bconst(b) {
            let n = vals.len() as i32;
            return self.konst(n);
        }
        self.intern(Op::BCount(b))
    }

    // ------------------------------------------------------------------ runtime signals

    /// Whether `v` is a runtime `Signal` value.
    pub fn is_sigval(&self, v: V) -> bool {
        match self.nodes[v as usize] {
            Op::SigOf(_) => true,
            Op::Src(s) => self.src_sig.get(s as usize).copied().unwrap_or(false),
            _ => false,
        }
    }

    /// A signal (runtime or constant) as its one-hot bundle; anything else unchanged.
    pub fn unsig(&mut self, v: V) -> V {
        match self.nodes[v as usize] {
            Op::SigOf(x) => x,
            Op::SigK(s) => self.bconst([(s, 1)]),
            _ => v,
        }
    }

    /// Marks one-hot bundle `b` as a runtime `Signal` value.
    pub fn sigval(&mut self, b: V) -> V {
        if self.is_sigval(b) {
            return b;
        }
        self.intern(Op::SigOf(b))
    }

    /// The signal of a bundle with (at most) one signal: that signal with value 1.
    pub fn onehot(&mut self, b: V) -> V {
        if let Some(vals) = self.as_bconst(b) {
            let one: BVals = vals.iter().map(|(s, _)| (*s, 1)).collect();
            let k = self.bconst(one);
            return self.sigval(k);
        }
        let z = self.konst(0);
        let nz = vec![vec![BLit { op: CmpOp::Ne, a: BOp::Each, b: BOp::Val(z) }]];
        let h = self.bun(vec![BTerm::Filter(b, nz, FOut::Const(1))]);
        self.sigval(h)
    }

    /// `Σ a[s] · b[s]`: with `b` one-hot, `a`'s value of `b`'s signal.
    pub fn bdot(&mut self, a: V, b: V) -> V {
        if let Some(vals) = self.as_bconst(b).cloned() {
            let mut acc = self.konst(0);
            for (s, k) in vals {
                let x = self.bget(a, s);
                let kv = self.konst(k);
                let t = self.ar(ArOp::Mul, x, kv);
                acc = self.ar(ArOp::Add, acc, t);
            }
            return acc;
        }
        if self.as_bconst(a).is_some() {
            return self.bdot(b, a);
        }
        self.intern(Op::BDot(a, b))
    }

    /// `b` with signal `s` (a one-hot bundle) set to `x`.
    pub fn bset_dyn(&mut self, b: V, s: V, x: V) -> V {
        if let Some(vals) = self.as_bconst(s).cloned() {
            return match vals.as_slice() {
                [] => b,
                [(sig, _)] => self.bset(b, *sig, x),
                _ => unreachable!("a signal value has one signal"),
            };
        }
        let z = self.konst(0);
        let missing = vec![vec![BLit { op: CmpOp::Eq, a: BOp::Each, b: BOp::Val(z) }]];
        self.bun(vec![BTerm::DFilter(b, s, missing, FOut::Copy), BTerm::Map(ArOp::Mul, s, x)])
    }

    /// Like [`Graph::brank`], with a runtime rank `k`.
    pub fn brank_at(&mut self, b: V, max: bool, k: V) -> V {
        if let Some(k) = self.as_const(k) {
            return if k < 0 { self.bconst([]) } else { self.brank(b, max, k as u32) };
        }
        let ix = self.bun(vec![BTerm::Shift(SignalTable::base().index_signal(), k, 0)]);
        self.intern(Op::BSelectAt(b, max, ix))
    }

    /// A selector mode applied to bundle `b` (folded when `b` is constant, except random picks).
    pub fn bsel(&mut self, b: V, mode: Selector) -> V {
        if let Some(vals) = self.as_bconst(b) {
            let t = SignalTable::base();
            let item = |s: Sig| t.info(s).kind == ticky_factorio::SignalKind::Item;
            let folded: Option<Vec<(Sig, i32)>> = match &mode {
                Selector::StackSize => Some(vals.iter().filter(|(s, _)| item(*s)).filter_map(|(s, _)| Some((*s, ticky_factorio::items::stack_size(t.name(*s))?))).collect()),
                Selector::RocketCapacity => {
                    Some(vals.iter().filter(|(s, _)| item(*s)).filter_map(|(s, _)| Some((*s, ticky_factorio::items::rocket_capacity(t.name(*s))?))).collect())
                }
                Selector::QualityFilter { cmp, q } => Some(vals.iter().filter(|(s, _)| cmp.apply(t.info(*s).quality as i32, *q as i32)).copied().collect()),
                Selector::QualitySet { q } => {
                    let mut m: Vec<(Sig, i32)> = Vec::new();
                    for (s, v) in vals.iter() {
                        let s = t.with_quality(*s, *q);
                        match m.iter_mut().find(|x| x.0 == s) {
                            Some(x) => x.1 = x.1.wrapping_add(*v),
                            None => m.push((s, *v)),
                        }
                    }
                    Some(m)
                }
                _ => None,
            };
            if let Some(v) = folded {
                return self.bconst(v.into_iter().filter(|x| x.1 != 0));
            }
        }
        let nonce = if matches!(mode, Selector::Random { .. }) {
            self.nonce += 1;
            self.nonce
        } else {
            0
        };
        self.intern(Op::BSel(b, mode, nonce))
    }

    pub fn bselect(&mut self, b: V, max: bool) -> V {
        self.brank(b, max, 0)
    }

    /// The signal ranked `index` by value (from the largest if `max`); nothing if there are
    /// fewer signals.
    pub fn brank(&mut self, b: V, max: bool, index: u32) -> V {
        if let Some(vals) = self.as_bconst(b) {
            let mut v = vals.clone();
            let t = SignalTable::base();
            if max {
                v.sort_by_key(|(s, x)| (std::cmp::Reverse(*x), t.rank(*s)));
            } else {
                v.sort_by_key(|(s, x)| (*x, std::cmp::Reverse(t.rank(*s))));
            }
            let one: BVals = v.get(index as usize).into_iter().copied().collect();
            return self.bconst(one);
        }
        self.intern(Op::BSelect(b, max, index))
    }

    // ------------------------------------------------------------------ signal arrays

    /// Element `k` of a signal array is on this signal.
    pub fn slot(k: usize) -> Sig {
        SignalTable::base().array_signals()[k]
    }

    /// `T[k] = k + 1` for the first `n` slots: positions, never 0.
    pub fn positions(&mut self, n: usize) -> V {
        self.bconst((0..n).map(|k| (Graph::slot(k), k as i32 + 1)))
    }

    /// `i + c` as `(x, c')` with constant offsets folded in.
    fn offset(&self, i: V, c: i32) -> (V, i32) {
        if let Op::Ar(op @ (ArOp::Add | ArOp::Sub), x, k) = *self.op(i) {
            if let Some(k) = self.as_const(k) {
                let k = if op == ArOp::Add { k } else { k.wrapping_neg() };
                return (x, c.wrapping_add(k));
            }
        }
        (i, c)
    }

    /// Element `i` of an `n`-element array bundle; 0 when `i` is out of range.
    pub fn aget(&mut self, b: V, i: V, n: usize) -> V {
        if let Some(k) = self.as_const(i) {
            return if (0..n as i64).contains(&(k as i64)) { self.bget(b, Graph::slot(k as usize)) } else { self.konst(0) };
        }
        let (x, c) = self.offset(i, 1);
        let r = SignalTable::base().index_signal();
        let pos = (0..n).map(|k| (Graph::slot(k), k as i32 + 1)).collect();
        let ix = self.bun(vec![BTerm::K(pos), BTerm::Shift(r, x, c)]);
        self.aget_ix(b, ix)
    }

    /// [`Op::AGet`] from its index bundle.
    pub fn aget_ix(&mut self, b: V, ix: V) -> V {
        if let (Some(bv), Some(iv)) = (self.as_bconst(b), self.as_bconst(ix)) {
            let r = SignalTable::base().index_signal();
            let i = bval(iv, r);
            let k = iv.iter().filter(|(s, v)| *s != r && *v == i).fold(0i32, |acc, (s, _)| acc.wrapping_add(bval(bv, *s)));
            return self.konst(k);
        }
        self.intern(Op::AGet(b, ix))
    }

    /// The one-hot bundle of index `i`: slot `i` set to `val`, or nothing out of range.
    pub fn ahot(&mut self, i: V, n: usize, val: i32) -> V {
        if let Some(k) = self.as_const(i) {
            let one = (0..n as i64).contains(&(k as i64)).then(|| (Graph::slot(k as usize), val));
            return self.bconst(one);
        }
        let (x, c) = self.offset(i, 1);
        let r = SignalTable::base().index_signal();
        let t = self.positions(n);
        let ix = self.bun(vec![BTerm::Shift(r, x, c)]);
        self.bun(vec![BTerm::Hot(t, ix, val)])
    }

    /// The terms of a bundle, to sum it with others on one wire.
    fn terms_of(&self, b: V) -> Vec<BTerm> {
        match self.op(b) {
            Op::Bun(t) => t.clone(),
            Op::BConst(vals) => vec![BTerm::K(vals.clone())],
            _ => unreachable!("a one-hot bundle is a constant or a bundle of terms"),
        }
    }

    /// `ahot(i) * x`.
    fn ahot_times(&mut self, i: V, n: usize, x: V) -> Vec<BTerm> {
        match self.as_const(x) {
            Some(k) => {
                let h = self.ahot(i, n, k);
                self.terms_of(h)
            }
            None => {
                let h = self.ahot(i, n, 1);
                vec![BTerm::Map(ArOp::Mul, h, x)]
            }
        }
    }

    /// Array bundle `b` with element `i` set to `x` (unchanged when `i` is out of range).
    pub fn aset(&mut self, b: V, i: V, x: V, n: usize) -> V {
        if let Some(k) = self.as_const(i) {
            if !(0..n as i64).contains(&(k as i64)) {
                return b;
            }
            return self.bset(b, Graph::slot(k as usize), x);
        }
        let h = self.ahot(i, n, 1);
        let z = self.konst(0);
        let keep = BTerm::DFilter(b, h, vec![vec![BLit { op: CmpOp::Eq, a: BOp::Each, b: BOp::Val(z) }]], FOut::Copy);
        let mut terms = vec![keep];
        terms.extend(self.ahot_times(i, n, x));
        self.bun(terms)
    }

    /// Array bundle `b` with `d` added to element `i`.
    pub fn aadd(&mut self, b: V, i: V, d: V, n: usize) -> V {
        let z = self.konst(0);
        let mut terms = vec![BTerm::Map(ArOp::Add, b, z)];
        terms.extend(self.ahot_times(i, n, d));
        if terms.len() == 1 {
            return b;
        }
        self.bun(terms)
    }

    /// `x` on every slot of an `n`-element array bundle that holds 0.
    pub fn azeros(&mut self, b: V, x: V, n: usize) -> V {
        let ones = self.bconst((0..n).map(|k| (Graph::slot(k), 1)));
        let z = self.konst(0);
        let zero = vec![vec![BLit { op: CmpOp::Eq, a: BOp::Each, b: BOp::Val(z) }]];
        match self.as_const(x) {
            Some(c) => self.bun(vec![BTerm::DFilter(ones, b, zero, FOut::Const(c))]),
            None => {
                let at = self.bun(vec![BTerm::DFilter(ones, b, zero, FOut::Copy)]);
                self.bun(vec![BTerm::Map(ArOp::Mul, at, x)])
            }
        }
    }

    /// The largest (or smallest) element of an `n`-element array bundle, zeros included.
    pub fn amax(&mut self, b: V, n: usize, max: bool) -> V {
        let best = self.bselect(b, max);
        let best = self.btotal(best);
        let count = self.bcount(b);
        let nk = self.konst(n as i32);
        let z = self.konst(0);
        let has_zero = self.cmp(CmpOp::Lt, count, nk);
        let beats = self.cmp(if max { CmpOp::Lt } else { CmpOp::Gt }, best, z);
        let zero = self.ar(ArOp::And, has_zero, beats);
        self.mux(zero, z, best)
    }

    /// An `n`-element array bundle sorted ascending (descending if `rev`). Sorts the keys
    /// `2x + 1`, which are never 0, so zeros take part; values must be within ±2^30.
    pub fn asorted(&mut self, b: V, n: usize, rev: bool) -> V {
        let two = self.konst(2);
        let ones = (0..n).map(|k| (Graph::slot(k), 1)).collect();
        let keys = self.bun(vec![BTerm::Map(ArOp::Mul, b, two), BTerm::K(ones)]);
        let mut terms = Vec::new();
        for k in 0..n {
            let r = self.brank(keys, rev, k as u32);
            terms.push(BTerm::Fold(r, ArOp::Shr, 1, Graph::slot(k)));
        }
        self.bun(terms)
    }

    /// Bundle select over mutually exclusive guards (see [`Op::BDec`]).
    pub fn bdec(&mut self, arms: Vec<(Dnf, V)>) -> V {
        let arms: Vec<(Dnf, V)> =
            arms.into_iter().filter(|(d, x)| !d.is_empty() && self.as_bconst(*x).is_none_or(|b| !b.is_empty())).collect();
        match arms.as_slice() {
            [] => self.bconst([]),
            [(d, x)] if d.iter().any(|t| t.is_empty()) => *x,
            _ => self.intern(Op::BDec(arms)),
        }
    }

    /// Bundle select from complementary conditions.
    pub fn bmux_tf(&mut self, t: V, f: V, a: V, b: V) -> V {
        if a == b {
            return a;
        }
        if let Some(k) = self.as_const(t) {
            return if k != 0 { a } else { b };
        }
        if let Some(k) = self.as_const(f) {
            return if k != 0 { b } else { a };
        }
        // Bundles made of single signals stay that way: select each signal's value.
        if let (Some(pa), Some(pb)) = (self.singles(a), self.singles(b)) {
            let (pa, pb) = (self.collect(pa), self.collect(pb));
            let mut sigs: Vec<Sig> = pa.keys().chain(pb.keys()).copied().collect();
            sigs.sort();
            sigs.dedup();
            // Only for a few signals (each becomes a decider or two; a bundle select costs a
            // decider per side however many signals).
            if sigs.len() > 8 {
                return self.intern(Op::BMux { t, f, a, b });
            }
            let z = self.konst(0);
            let mut terms = Vec::new();
            for s in sigs {
                let (x, y) = (pa.get(&s).copied().unwrap_or(z), pb.get(&s).copied().unwrap_or(z));
                let m = self.mux_tf(t, f, x, y);
                terms.push(BTerm::One(s, m));
            }
            return self.bun(terms);
        }
        self.intern(Op::BMux { t, f, a, b })
    }

    /// Each signal's total, as scalar nodes.
    fn collect(&mut self, parts: Vec<(Sig, Result<V, i32>)>) -> BTreeMap<Sig, V> {
        let mut by: BTreeMap<Sig, Vec<Result<V, i32>>> = BTreeMap::new();
        for (s, p) in parts {
            by.entry(s).or_default().push(p);
        }
        by.into_iter().map(|(s, ps)| (s, self.sum_parts(ps))).collect()
    }

    /// `b` with signal `s` set to `x` (Python `b[s] = x`).
    pub fn bset(&mut self, b: V, s: Sig, x: V) -> V {
        if let Some(parts) = self.singles(b) {
            let mut m = self.collect(parts);
            m.insert(s, x);
            let terms = m.into_iter().map(|(s, v)| BTerm::One(s, v)).collect();
            return self.bun(terms);
        }
        let z = self.konst(0);
        // Write combining: if `b` is itself `b0` with some signals set, set this one on `b0`
        // too (replacing an earlier write to it), so a run of writes stays one stage deep.
        if let Op::Bun(terms) = self.op(b).clone() {
            let base = terms.iter().find_map(|t| match t {
                BTerm::Map(ArOp::Add, b0, k) if *k == z => Some(*b0),
                _ => None,
            });
            if let Some(b0) = base {
                let sets_on_b0 = |t: &BTerm| matches!(t, BTerm::Set(bb, _, _) if *bb == b0) || matches!(t, BTerm::Map(ArOp::Add, bb, k) if *bb == b0 && *k == z);
                if terms.iter().all(sets_on_b0) {
                    let mut new: Vec<BTerm> = terms.into_iter().filter(|t| !matches!(t, BTerm::Set(_, s2, _) if *s2 == s)).collect();
                    new.push(BTerm::Set(b0, s, x));
                    return self.bun(new);
                }
            }
        }
        self.bun(vec![BTerm::Map(ArOp::Add, b, z), BTerm::Set(b, s, x)])
    }

    /// The bundle mux shape `(t, f, a, b)` of a node, scalar or bundle.
    pub fn as_mux(&self, v: V) -> Option<(V, V, V, V)> {
        match *self.op(v) {
            Op::Mux { t, f, a, b } | Op::BMux { t, f, a, b } => Some((t, f, a, b)),
            _ => None,
        }
    }

    pub fn operands(&self, v: V) -> Vec<V> {
        match *self.op(v) {
            Op::Const(_) | Op::Src(_) => vec![],
            Op::Ar(_, a, b) | Op::Cmp(_, a, b) => vec![a, b],
            Op::Mux { t, f, a, b } => vec![t, f, a, b],
            Op::Dec(ref arms) => arms.iter().flat_map(|(d, _)| dnf_operands(d)).collect(),
            Op::Sel(ref arms) => arms.iter().flat_map(|(c, v)| [*c, *v]).collect(),
            Op::BConst(_) | Op::Each | Op::SigK(_) => vec![],
            Op::Bun(ref terms) => terms.iter().flat_map(|t| t.operands()).collect(),
            Op::BMux { t, f, a, b } => vec![t, f, a, b],
            Op::BDec(ref arms) => arms.iter().flat_map(|(d, x)| dnf_operands(d).into_iter().chain([*x])).collect(),
            Op::BSelect(b, ..) | Op::BGet(b, _) | Op::BTotal(b) | Op::BCount(b) | Op::SigOf(b) | Op::BSel(b, ..) => vec![b],
            Op::AGet(b, ix) | Op::BSelectAt(b, _, ix) | Op::BDot(b, ix) => vec![b, ix],
        }
    }

    /// Combinator depth: sources and constants are 0, every other node is 1 + its deepest operand.
    pub fn depths(&self) -> Vec<u32> {
        let mut d = vec![0u32; self.nodes.len()];
        // Operands always precede their users.
        for v in 0..self.nodes.len() as V {
            let ops = self.operands(v);
            if !ops.is_empty() {
                d[v as usize] = 1 + ops.iter().map(|o| d[*o as usize]).max().unwrap();
            }
        }
        d
    }

    /// Nodes reachable from `roots`, in topological (creation) order.
    pub fn reachable(&self, roots: &[V]) -> Vec<V> {
        let mut seen = vec![false; self.nodes.len()];
        let mut stack: Vec<V> = roots.to_vec();
        while let Some(v) = stack.pop() {
            if std::mem::replace(&mut seen[v as usize], true) {
                continue;
            }
            stack.extend(self.operands(v));
        }
        (0..self.nodes.len() as V).filter(|v| seen[*v as usize]).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn folding_and_intervals() {
        let mut g = Graph::new(vec![Iv { lo: 0, hi: 599 }]);
        let x = g.src(0);
        let one = g.konst(1);
        let x1 = g.ar(ArOp::Add, x, one);
        assert_eq!(g.iv(x1), Iv { lo: 1, hi: 600 });
        let k = g.konst(600);
        let m = g.ar(ArOp::Mod, x1, k);
        assert_eq!(g.iv(m), Iv { lo: 0, hi: 599 });
        // x < 1000 is always true for x in [0, 599].
        let big = g.konst(1000);
        let lt = g.cmp(CmpOp::Lt, x, big);
        assert_eq!(g.as_const(lt), Some(1));
        let (two, three) = (g.konst(2), g.konst(3));
        let six = g.ar(ArOp::Mul, two, three);
        assert_eq!(g.as_const(six), Some(6));
        let zero = g.konst(0);
        assert_eq!(g.ar(ArOp::Add, x, zero), x);
    }
}
