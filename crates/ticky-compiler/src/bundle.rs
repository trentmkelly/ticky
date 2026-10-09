//! Bundles (everything on a wire) in expressions: signal names, element-wise arithmetic and
//! dict comprehensions, lowered to per-signal combinator operations (`each`).
//!
//! A comprehension `{s: f(v) for s, v in b.items() if c(v)}` is lowered with `v` standing
//! for a placeholder node ([`Op::Each`]); the resulting scalar expression is then turned
//! into bundle operations over the *domain*: the signals of `b` that pass `c`. Every
//! intermediate bundle holds the value of a subexpression for the domain's signals, where
//! a missing signal means 0, so operations that turn 0 into something else (`x + 1`) add
//! the domain explicitly.

use std::cell::RefCell;

use ticky_factorio::{ArOp, CmpOp, Sig, SignalKind, SignalTable};
use ticky_syntax::ast::{BinOp, Expr, ExprKind};
use ticky_syntax::{Diag, Span};

use crate::ir::{BDnf, BLit, BOp, BTerm, FOut, Graph, Op, V};
use crate::lower::{self, Names};

thread_local! {
    static WARNINGS: RefCell<Vec<Diag>> = const { RefCell::new(Vec::new()) };
}

/// Records a warning (deduplicated when taken).
pub fn warn(d: Diag) {
    WARNINGS.with(|w| w.borrow_mut().push(d));
}

/// Warnings recorded since the last call, without duplicates.
pub fn take_warnings() -> Vec<Diag> {
    let all = WARNINGS.with(|w| std::mem::take(&mut *w.borrow_mut()));
    let mut out: Vec<Diag> = Vec::new();
    for d in all {
        if !out.iter().any(|o| o.span == d.span && o.message == d.message) {
            out.push(d);
        }
    }
    out
}

fn unknown(sig: Sig, span: Span) -> Sig {
    let t = SignalTable::base();
    let info = t.info(sig);
    if !info.known {
        warn(Diag::warning(span, format!("unknown signal {} \"{}\"", info.kind.as_str(), info.name)).with_help(
            "it isn't in the base game or Space Age; fine for a modded signal, but check the spelling",
        ));
    }
    sig
}

/// A signal by exact name, optionally with its type (`item` when unknown and unspecified).
pub fn exact(name: &str, kind: Option<SignalKind>, span: Span) -> Sig {
    let t = SignalTable::base();
    let s = match kind {
        Some(k) => t.intern(k, name),
        None => t.lookup(name).unwrap_or_else(|| t.intern(SignalKind::Item, name)),
    };
    unknown(s, span)
}

/// A signal written as an identifier: `iron_plate`, `A`, `red`.
pub fn ident(name: &str, span: Span) -> Sig {
    let t = SignalTable::base();
    match t.resolve_ident(name) {
        Some(s) => s,
        None => {
            let s = t.intern(SignalKind::Item, &name.replace('_', "-"));
            let help = format!("for an exact name (or another type) write S(\"{}\") or S(\"…\", type=\"recipe\")", t.name(s));
            if !t.info(s).known {
                warn(Diag::warning(span, format!("unknown signal `{name}`, read as item \"{}\"", t.name(s))).with_help(help));
            }
            s
        }
    }
}

/// `S("name", type="recipe")`.
pub fn s_call(args: &[Expr], kwargs: &[(String, Expr)], span: Span) -> Result<Sig, Diag> {
    let [Expr { kind: ExprKind::Str(name), .. }] = args else {
        return Err(Diag::error(span, "`S` takes a signal name in quotes, e.g. S(\"iron-plate\")"));
    };
    let mut kind = None;
    let mut quality = 0u8;
    for (k, v) in kwargs {
        match (k.as_str(), &v.kind) {
            ("type", ExprKind::Str(t)) => {
                kind = Some(SignalKind::parse(t).ok_or_else(|| {
                    Diag::error(v.span, format!("unknown signal type \"{t}\""))
                        .with_help("use \"item\", \"fluid\", \"virtual\", \"recipe\", \"quality\", \"space-location\" or \"asteroid-chunk\"")
                })?);
            }
            ("quality", ExprKind::Str(q)) => {
                quality = ticky_factorio::QUALITIES.iter().position(|x| x == q).ok_or_else(|| {
                    Diag::error(v.span, format!("unknown quality \"{q}\"")).with_help("use \"normal\", \"uncommon\", \"rare\", \"epic\" or \"legendary\"")
                })? as u8;
            }
            _ => return Err(Diag::error(v.span, format!("`S` doesn't take `{k}`"))),
        }
    }
    let sig = exact(name, kind, span);
    Ok(SignalTable::base().with_quality(sig, quality))
}

/// What a value is.
#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Kind {
    Int,
    Bundle,
    /// A signal known when compiling (`S("iron-plate")`).
    Signal,
    /// A signal only known at run time (`b.argmax()`, a `Signal` variable): a one-hot bundle.
    SigVal,
}

impl Kind {
    /// Either kind of signal.
    pub fn is_signal(self) -> bool {
        matches!(self, Kind::Signal | Kind::SigVal)
    }
}

pub fn kind(g: &Graph, v: V) -> Kind {
    if g.is_sigval(v) {
        Kind::SigVal
    } else if g.is_bundle(v) {
        Kind::Bundle
    } else if g.as_sig(v).is_some() {
        Kind::Signal
    } else {
        Kind::Int
    }
}

/// Requires a number.
pub fn int(g: &Graph, v: V, span: Span) -> Result<V, Diag> {
    match kind(g, v) {
        Kind::Int => Ok(v),
        Kind::Bundle => Err(Diag::error(span, "expected a number, but this is a bundle")
            .with_help("read one signal with `b[S(\"name\")]` or `b.name`, or reduce it with `b.total()`, `len(b)` or `max(b.values())`")),
        Kind::Signal | Kind::SigVal => Err(Diag::error(span, "expected a number, but this is a signal")
            .with_help("signals name bundle entries, e.g. `stock[sig]`")),
    }
}

/// A bundle key: a signal known when compiling, or a runtime signal (its one-hot bundle).
pub enum Key {
    Const(Sig),
    Dyn(V),
}

/// A key for indexing that may be a runtime signal.
pub fn key_any(g: &mut Graph, names: &mut dyn Names, e: &Expr) -> Result<Key, Diag> {
    if let ExprKind::Str(n) = &e.kind {
        return Ok(Key::Const(exact(n, None, e.span)));
    }
    let v = lower::expr(g, names, e)?;
    match kind(g, v) {
        Kind::Signal => Ok(Key::Const(g.as_sig(v).unwrap())),
        Kind::SigVal => Ok(Key::Dyn(g.unsig(v))),
        _ => Err(Diag::error(e.span, "expected a signal here").with_help("write S(\"name\"), a signal constant or a `Signal` value")),
    }
}

/// `b[k]`.
pub fn get(g: &mut Graph, b: V, k: Key) -> V {
    match k {
        Key::Const(s) => g.bget(b, s),
        Key::Dyn(h) => g.bdot(b, h),
    }
}

/// `b` with `b[k] = x`.
pub fn set(g: &mut Graph, b: V, k: Key, x: V) -> V {
    match k {
        Key::Const(s) => g.bset(b, s, x),
        Key::Dyn(h) => g.bset_dyn(b, h, x),
    }
}

pub fn bundle(g: &Graph, v: V, span: Span) -> Result<V, Diag> {
    match kind(g, v) {
        Kind::Bundle => Ok(v),
        _ => Err(Diag::error(span, "expected a bundle here")),
    }
}

pub fn signal(g: &Graph, v: V, span: Span) -> Result<Sig, Diag> {
    g.as_sig(v).ok_or_else(|| {
        Diag::error(span, "expected a signal here").with_help("write S(\"name\"), or a constant set to one")
    })
}

fn arop(op: BinOp) -> ArOp {
    match op {
        BinOp::Add => ArOp::Add,
        BinOp::Sub => ArOp::Sub,
        BinOp::Mul => ArOp::Mul,
        BinOp::FloorDiv => ArOp::Div,
        BinOp::Mod => ArOp::Mod,
        BinOp::Pow => ArOp::Pow,
        BinOp::Shl => ArOp::Shl,
        BinOp::Shr => ArOp::Shr,
        BinOp::BitAnd => ArOp::And,
        BinOp::BitOr => ArOp::Or,
        BinOp::BitXor => ArOp::Xor,
        BinOp::Div => unreachable!("rejected earlier"),
    }
}

/// `a op b` where at least one side is a bundle.
pub fn binop(g: &mut Graph, op: BinOp, a: V, b: V, span: Span) -> Result<V, Diag> {
    let (ka, kb) = (kind(g, a), kind(g, b));
    if ka.is_signal() || kb.is_signal() {
        return Err(Diag::error(span, "signals can't be used in arithmetic"));
    }
    let o = arop(op);
    Ok(match (ka, kb) {
        // Sums of small computed bundles share one wire: no extra combinator or tick (the
        // terms are duplicated if a part is also used elsewhere, so only small ones).
        (Kind::Bundle, Kind::Bundle) if o == ArOp::Add && terms_len(g, a) + terms_len(g, b) <= 4 => merge(g, a, b),
        (Kind::Bundle, Kind::Bundle) => g.bun(vec![BTerm::Zip(o, a, b)]),
        (Kind::Bundle, _) => {
            each_scalar_warning(g, o, b, span);
            g.bun(vec![BTerm::Map(o, a, b)])
        }
        _ if o.commutative() => {
            each_scalar_warning(g, o, a, span);
            g.bun(vec![BTerm::Map(o, b, a)])
        }
        _ => {
            each_scalar_warning(g, o, a, span);
            g.bun(vec![BTerm::RMap(o, a, b)])
        }
    })
}

fn each_scalar_warning(g: &Graph, op: ArOp, k: V, span: Span) {
    if matches!(op, ArOp::Add | ArOp::Sub | ArOp::Or | ArOp::Xor) && g.as_const(k) != Some(0) {
        warn(Diag::warning(span, "a bundle combined with a number only changes the signals it already has")
            .with_help("Factorio's `each` skips missing signals, so `b + 5` doesn't add signals; to include more, combine two bundles, e.g. `WANT - stock`"));
    }
}

/// `a == b` / `a != b` on bundles: equal when their difference has no signals.
pub fn equal(g: &mut Graph, a: V, b: V, eq: bool) -> V {
    let d = g.bun(vec![BTerm::Zip(ArOp::Sub, a, b)]);
    let n = g.bcount(d);
    let z = g.konst(0);
    g.cmp(if eq { CmpOp::Eq } else { CmpOp::Ne }, n, z)
}

/// `Bundle(...)`: from a bundle or dict (positional) and/or `name=value` pairs.
pub fn construct(g: &mut Graph, names: &mut dyn Names, args: &[Expr], kwargs: &[(String, Expr)], span: Span) -> Result<V, Diag> {
    if args.len() > 1 {
        return Err(Diag::error(span, "`Bundle` takes at most one positional argument (a bundle or a dict)"));
    }
    let mut parts = Vec::new();
    if let Some(a) = args.first() {
        let v = lower::expr(g, names, a)?;
        let v = bundle(g, v, a.span)?;
        let e = g.empty_bundle();
        parts.push(BTerm::Zip(ArOp::Add, v, e));
    }
    for (k, e) in kwargs {
        let sig = ident(k, e.span);
        let v = lower::expr(g, names, e)?;
        parts.push(BTerm::One(sig, int(g, v, e.span)?));
    }
    Ok(sum_terms(g, parts))
}

/// Sums terms; plain bundle copies (`Zip(+, b, empty)`) are used as they are when alone.
fn sum_terms(g: &mut Graph, parts: Vec<BTerm>) -> V {
    match parts.as_slice() {
        [] => g.empty_bundle(),
        [BTerm::Zip(ArOp::Add, b, _)] => *b,
        _ => g.bun(parts),
    }
}

/// A dict literal: keys are signal names in quotes or signal values.
pub fn dict(g: &mut Graph, names: &mut dyn Names, items: &[(Expr, Expr)]) -> Result<V, Diag> {
    let mut last: Vec<(Sig, V)> = Vec::new();
    let mut keys = Vec::new();
    for (k, e) in items {
        let key = key_any(g, names, k)?;
        let v = lower::expr(g, names, e)?;
        keys.push((key, int(g, v, e.span)?));
    }
    // Runtime keys may equal each other or a constant key: set them one by one.
    if keys.iter().any(|(k, _)| matches!(k, Key::Dyn(_))) {
        let mut acc = g.empty_bundle();
        for (k, v) in keys {
            acc = set(g, acc, k, v);
        }
        return Ok(acc);
    }
    for (key, v) in keys {
        let Key::Const(sig) = key else { unreachable!() };
        // Like a Python dict, a repeated key keeps its last value.
        last.retain(|(s, _)| *s != sig);
        last.push((sig, v));
    }
    let terms = last.into_iter().map(|(s, v)| BTerm::One(s, v)).collect();
    Ok(g.bun(terms))
}

/// A key for indexing: a name in quotes or a signal value.
pub fn key(g: &mut Graph, names: &mut dyn Names, e: &Expr) -> Result<Sig, Diag> {
    match &e.kind {
        ExprKind::Str(n) => Ok(exact(n, None, e.span)),
        _ => {
            let v = lower::expr(g, names, e)?;
            signal(g, v, e.span)
        }
    }
}

/// Names inside a comprehension: `v` is the placeholder, `s` is only allowed as the key.
struct CompNames<'a> {
    inner: &'a mut dyn Names,
    s: &'a str,
    v: &'a str,
    each: V,
}

impl Names for CompNames<'_> {
    fn lookup(&mut self, g: &mut Graph, name: &str, span: Span) -> Result<V, Diag> {
        if name == self.v {
            return Ok(self.each);
        }
        if name == self.s {
            return Err(Diag::error(span, format!("`{}` (the signal) can only be used as the key", crate::expand::display(self.s)))
                .with_help("the comprehension runs on every signal at once, so values can depend on `v` but not on which signal it is"));
        }
        self.inner.lookup(g, name, span)
    }

    fn ticks(&mut self, g: &mut Graph, span: Span) -> Result<V, Diag> {
        self.inner.ticks(g, span)
    }
}

/// `{s: value for s, v in b.items() if cond…}`.
#[allow(clippy::too_many_arguments)]
pub fn comprehension(
    g: &mut Graph,
    names: &mut dyn Names,
    key: &Expr,
    value: &Expr,
    target: &Expr,
    iter: &Expr,
    conds: &[Expr],
    span: Span,
) -> Result<V, Diag> {
    let shape_help = "write it as `{s: v for s, v in b.items() if …}`";
    let ExprKind::Tuple(t) = &target.kind else {
        return Err(Diag::error(target.span, "a bundle comprehension needs two names: `for s, v in b.items()`").with_help(shape_help));
    };
    let [Expr { kind: ExprKind::Name(s), .. }, Expr { kind: ExprKind::Name(v), .. }] = t.as_slice() else {
        return Err(Diag::error(target.span, "a bundle comprehension needs two names: `for s, v in b.items()`").with_help(shape_help));
    };
    let ExprKind::Call { func, args, kwargs } = &iter.kind else {
        return Err(Diag::error(iter.span, "bundle comprehensions iterate over `b.items()`").with_help(shape_help));
    };
    let ExprKind::Attr(base, m) = &func.kind else {
        return Err(Diag::error(iter.span, "bundle comprehensions iterate over `b.items()`").with_help(shape_help));
    };
    if m != "items" || !args.is_empty() || !kwargs.is_empty() {
        return Err(Diag::error(iter.span, "bundle comprehensions iterate over `b.items()`").with_help(shape_help));
    }
    if !matches!(&key.kind, ExprKind::Name(k) if k == s) {
        return Err(Diag::error(key.span, format!("the key must be `{}`, the signal", crate::expand::display(s)))
            .with_help("the result has the same signals as the input (or fewer, with `if`)"));
    }
    let b = lower::expr(g, names, base)?;
    let b = bundle(g, b, base.span)?;
    let each = g.each();
    let mut cn = CompNames { inner: names, s, v, each };
    // The domain: the input's signals that pass every condition.
    let mut dom = b;
    for c in conds {
        let cv = lower::expr(g, &mut cn, c)?;
        let cv = int(g, cv, c.span)?;
        let cv = g.truth(cv);
        dom = Conv { dom, each, span: c.span }.restrict(g, cv, false)?;
    }
    let x = lower::expr(g, &mut cn, value)?;
    let x = int(g, x, value.span)?;
    let _ = span;
    Conv { dom, each, span: value.span }.bundle(g, x)
}

fn uses_each(g: &Graph, v: V) -> bool {
    g.uses_each(v)
}

const MAX_TERMS: usize = 12;

fn and(a: &BDnf, b: &BDnf) -> Option<BDnf> {
    let mut out = Vec::new();
    for x in a {
        for y in b {
            out.push(x.iter().chain(y.iter()).copied().collect());
        }
    }
    (out.len() <= MAX_TERMS).then_some(out)
}

fn or(a: BDnf, b: BDnf) -> Option<BDnf> {
    let mut out = a;
    out.extend(b);
    (out.len() <= MAX_TERMS).then_some(out)
}

fn negate(d: &BDnf) -> Option<BDnf> {
    let mut acc: BDnf = vec![vec![]];
    for t in d {
        let not_t: BDnf = t.iter().map(|l| vec![BLit { op: l.op.negate(), ..*l }]).collect();
        acc = and(&acc, &not_t)?;
    }
    Some(acc)
}

fn too_big(span: Span) -> Diag {
    Diag::error(span, "this condition is too complicated for one decider").with_help("split it into simpler conditions")
}

/// A per-signal condition (a boolean node) as decider conditions.
fn each_dnf(g: &mut Graph, c: V, span: Span) -> Result<BDnf, Diag> {
    if let Some(k) = g.as_const(c) {
        return Ok(if k != 0 { vec![vec![]] } else { vec![] });
    }
    if !uses_each(g, c) {
        let z = g.konst(0);
        return Ok(vec![vec![BLit { op: CmpOp::Ne, a: BOp::Val(c), b: BOp::Val(z) }]]);
    }
    let each = g.each();
    match g.op(c).clone() {
        // `not x` on a compound condition.
        Op::Cmp(CmpOp::Eq, x, z) if g.as_const(z) == Some(0) && g.is_bool(x) && !matches!(g.op(x), Op::Each) => {
            let d = each_dnf(g, x, span)?;
            negate(&d).ok_or_else(|| too_big(span))
        }
        Op::Cmp(op, a, b) => {
            let lit = match (a == each, b == each) {
                (true, false) if !uses_each(g, b) => BLit { op, a: BOp::Each, b: BOp::Val(b) },
                (false, true) if !uses_each(g, a) => BLit { op: op.flip(), a: BOp::Each, b: BOp::Val(a) },
                _ => {
                    return Err(Diag::error(span, "conditions in a bundle comprehension can only compare `v` itself")
                        .with_help("compare `v` with an expression that doesn't use `v`, e.g. `v * 2 > limit` → `v > limit // 2`"))
                }
            };
            Ok(vec![vec![lit]])
        }
        Op::Ar(ArOp::And, x, y) if g.is_bool(x) && g.is_bool(y) => {
            let (dx, dy) = (each_dnf(g, x, span)?, each_dnf(g, y, span)?);
            and(&dx, &dy).ok_or_else(|| too_big(span))
        }
        Op::Ar(ArOp::Or, x, y) if g.is_bool(x) && g.is_bool(y) => {
            let (dx, dy) = (each_dnf(g, x, span)?, each_dnf(g, y, span)?);
            or(dx, dy).ok_or_else(|| too_big(span))
        }
        Op::Mux { t, f, a, b } if g.is_bool(a) && g.is_bool(b) => {
            let (dt, df) = (each_dnf(g, t, span)?, each_dnf(g, f, span)?);
            let (da, db) = (each_dnf(g, a, span)?, each_dnf(g, b, span)?);
            let l = and(&dt, &da).ok_or_else(|| too_big(span))?;
            let r = and(&df, &db).ok_or_else(|| too_big(span))?;
            or(l, r).ok_or_else(|| too_big(span))
        }
        _ => Err(Diag::error(span, "this per-signal condition isn't supported")
            .with_help("use comparisons of `v` combined with `and`, `or` and `not`")),
    }
}

/// Turns a scalar expression of the placeholder into a bundle over the domain.
struct Conv {
    dom: V,
    each: V,
    span: Span,
}

impl Conv {
    fn unsupported(&self) -> Diag {
        Diag::error(self.span, "this per-signal expression isn't supported")
            .with_help("use `v` with numbers and +, -, *, //, %, &, |, ^, min, max, abs and `x if cond else y`")
    }

    /// A scalar (not using `v`) on every signal of the domain.
    fn scalar(&self, g: &mut Graph, k: V) -> V {
        let z = g.konst(0);
        let all: BDnf = vec![vec![BLit { op: CmpOp::Ne, a: BOp::Each, b: BOp::Val(z) }]];
        match g.as_const(k) {
            Some(c) => g.bun(vec![BTerm::Filter(self.dom, all, FOut::Const(c))]),
            None => {
                let ones = g.bun(vec![BTerm::Filter(self.dom, all, FOut::Const(1))]);
                g.bun(vec![BTerm::Map(ArOp::Mul, ones, k)])
            }
        }
    }

    fn with(&self, dom: V) -> Conv {
        Conv { dom, each: self.each, span: self.span }
    }

    /// The domain's signals where the per-signal condition `c` holds (fails, if `neg`).
    fn restrict(&self, g: &mut Graph, c: V, neg: bool) -> Result<V, Diag> {
        // Conditions on `v` itself (and on numbers) fit one filter decider.
        if let Ok(d) = each_dnf(g, c, self.span) {
            let d = if neg { negate(&d).ok_or_else(|| too_big(self.span))? } else { d };
            return Ok(g.bun(vec![BTerm::Filter(self.dom, d, FOut::Copy)]));
        }
        match g.op(c).clone() {
            Op::Cmp(CmpOp::Eq, x, z) if g.as_const(z) == Some(0) && g.is_bool(x) => self.restrict(g, x, !neg),
            Op::Cmp(op, a, b) => {
                // Compare the difference with 0, on every signal of the domain.
                let op = if neg { op.negate() } else { op };
                let diff = g.ar(ArOp::Sub, a, b);
                let db = self.bundle(g, diff)?;
                let z = g.konst(0);
                let d = vec![vec![BLit { op, a: BOp::Each, b: BOp::Val(z) }]];
                Ok(g.bun(vec![BTerm::DFilter(self.dom, db, d, FOut::Copy)]))
            }
            Op::Ar(op @ (ArOp::And | ArOp::Or), x, y) if g.is_bool(x) && g.is_bool(y) => {
                // x ∧ y: restrict twice. x ∨ y: the signals passing x, plus those failing x
                // but passing y (disjoint, so their sum).
                let both = (op == ArOp::And) != neg;
                if both {
                    let first = self.restrict(g, x, neg)?;
                    self.with(first).restrict(g, y, neg)
                } else {
                    let pass = self.restrict(g, x, neg)?;
                    let fail = self.restrict(g, x, !neg)?;
                    let rest = self.with(fail).restrict(g, y, neg)?;
                    Ok(merge(g, pass, rest))
                }
            }
            Op::Mux { t, a, b, .. } if g.is_bool(a) && g.is_bool(b) => {
                let (dt, df) = (self.restrict(g, t, false)?, self.restrict(g, t, true)?);
                let l = self.with(dt).restrict(g, a, neg)?;
                let r = self.with(df).restrict(g, b, neg)?;
                Ok(merge(g, l, r))
            }
            _ => Err(Diag::error(self.span, "this per-signal condition isn't supported")
                .with_help("use comparisons combined with `and`, `or` and `not`")),
        }
    }

    /// `x` over the domain's signals where `c` holds.
    fn select(&self, g: &mut Graph, c: V, neg: bool, x: V) -> Result<V, Diag> {
        let dom = self.restrict(g, c, neg)?;
        self.with(dom).bundle(g, x)
    }

    fn bundle(&self, g: &mut Graph, x: V) -> Result<V, Diag> {
        if x == self.each {
            return Ok(self.dom);
        }
        if !uses_each(g, x) {
            return Ok(self.scalar(g, x));
        }
        match g.op(x).clone() {
            Op::Ar(ArOp::And | ArOp::Or, a, b) if g.is_bool(a) && g.is_bool(b) => {
                let one = g.konst(1);
                self.select(g, x, false, one)
            }
            Op::Ar(op, a, b) => {
                // Operations that keep 0 at 0 can skip missing signals; `v` itself is never 0.
                let keeps_zero = matches!(op, ArOp::Mul | ArOp::Div | ArOp::Mod | ArOp::And | ArOp::Shl | ArOp::Shr);
                match (uses_each(g, a), uses_each(g, b)) {
                    (true, false) => {
                        let ab = self.bundle(g, a)?;
                        if keeps_zero || a == self.each {
                            Ok(g.bun(vec![BTerm::Map(op, ab, b)]))
                        } else {
                            let kb = self.scalar(g, b);
                            Ok(g.bun(vec![BTerm::Zip(op, ab, kb)]))
                        }
                    }
                    (false, true) if op.commutative() => {
                        let swapped = g.ar(op, b, a);
                        self.bundle(g, swapped)
                    }
                    (false, true) => {
                        let bb = self.bundle(g, b)?;
                        if b == self.each || matches!(op, ArOp::Div | ArOp::Mod) {
                            Ok(g.bun(vec![BTerm::RMap(op, a, bb)]))
                        } else if op == ArOp::Sub {
                            let ka = self.scalar(g, a);
                            Ok(g.bun(vec![BTerm::Zip(ArOp::Sub, ka, bb)]))
                        } else {
                            Err(self.unsupported())
                        }
                    }
                    (true, true) if op != ArOp::Pow => {
                        let (ab, bb) = (self.bundle(g, a)?, self.bundle(g, b)?);
                        Ok(g.bun(vec![BTerm::Zip(op, ab, bb)]))
                    }
                    _ => Err(self.unsupported()),
                }
            }
            Op::Mux { t, a, b, .. } => {
                let (xa, xb) = (self.select(g, t, false, a)?, self.select(g, t, true, b)?);
                Ok(merge(g, xa, xb))
            }
            Op::Cmp(..) => {
                let one = g.konst(1);
                self.select(g, x, false, one)
            }
            _ => Err(self.unsupported()),
        }
    }
}

fn terms_len(g: &Graph, v: V) -> usize {
    match g.op(v) {
        Op::Bun(t) => t.len(),
        Op::BConst(_) => 1,
        _ => 99,
    }
}

/// The sum of two bundles; two single-wire results share one wire without an extra tick.
fn merge(g: &mut Graph, a: V, b: V) -> V {
    let terms = |g: &Graph, v: V| match g.op(v) {
        Op::Bun(t) => Some(t.clone()),
        Op::BConst(k) => Some(vec![BTerm::K(k.clone())]),
        _ => None,
    };
    if let (Some(mut x), Some(y)) = (terms(g, a), terms(g, b)) {
        x.extend(y);
        return g.bun(x);
    }
    if g.as_bconst(a).is_some_and(|x| x.is_empty()) {
        return b;
    }
    if g.as_bconst(b).is_some_and(|x| x.is_empty()) {
        return a;
    }
    g.bun(vec![BTerm::Zip(ArOp::Add, a, b)])
}
