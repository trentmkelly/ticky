//! Vectorised range comprehensions: `[f(k, x…) for k in range(…)]`, where `f` is per-element
//! arithmetic on `k` and loop-invariant scalars, as bundle operations on the position table
//! instead of `n` scalar copies (SPEC §11.2).
//!
//! The comprehension is still unrolled into its elements: a register array, or anything that
//! reads the elements, takes those. The vectorised banks are recorded next to them and used
//! when the elements would be built into a signal array's banks ([`Expander::banks_of`]).
//!
//! A bank is `{s: f(c + step·v) for s, v in #aidx(nb).items()}`. The position table holds
//! `k + 1` on slot `k`, never 0, so every slot is in the comprehension's domain and no element
//! needs `mem_map`'s fix-up for zeros. Inside a bundle comprehension `//` and `%` truncate,
//! so Python's floor versions (by constants) are rewritten with `tdiv`/`tmod`.

use super::*;

/// Fewest elements that aren't constants or names for the bundle version to pay: below that
/// the unrolled table is a constant combinator plus copies.
const MIN_COMPUTED: usize = 2;
/// Fewest arithmetic operations on the range variable per element for which an array assigned
/// from the comprehension is made a signal array: unrolled into registers, each element costs about
/// that many combinators, as a signal array the bundle version plus a read per constant index.
const MIN_OPS: usize = 2;

/// A recorded bundle version of a range comprehension.
pub(super) struct Vectorised {
    /// The unrolled elements' `Debug` text.
    key: String,
    banks: Vec<Expr>,
    /// Whether an array assigned from it should be a signal array (see [`MIN_OPS`]).
    pub(super) signal_array: bool,
}

/// Arithmetic operations in `e` whose value depends on `var`; `None` if a comparison, select,
/// `min`, `max` or `abs` does (those take filter deciders per step in a bundle).
fn arithmetic_on(e: &Expr, var: &str) -> Option<usize> {
    let (mut n, mut other) = (0, false);
    visit(e, &mut |x| {
        if mentions(x, var) {
            match &x.kind {
                ExprKind::Binary(..) | ExprKind::Unary(..) => n += 1,
                ExprKind::Name(_) | ExprKind::Int(_) | ExprKind::Bool(_) => {}
                _ => other = true,
            }
        }
    });
    (!other).then_some(n)
}

/// Whether `e` uses `var` only in ways a bundle comprehension can compute per signal (checked
/// before expanding it again: with `var` not a constant, `xs[var]` would be a runtime read and
/// make `xs` a signal array). Like [`per_element`], with `//`, `%`, `tdiv` and `tmod`.
fn elementwise(e: &Expr, var: &str) -> bool {
    if !mentions(e, var) {
        return true;
    }
    let ok = |x: &Expr| elementwise(x, var);
    match &e.kind {
        ExprKind::Name(_) => true,
        ExprKind::Unary(_, a) | ExprKind::Not(a) => ok(a),
        ExprKind::Binary(op, a, b) => !matches!(op, BinOp::Pow | BinOp::Div) && ok(a) && ok(b),
        ExprKind::Compare(a, rest) => {
            rest.len() == 1 && !matches!(rest[0].0, CmpOp::In | CmpOp::NotIn) && ok(a) && ok(&rest[0].1)
        }
        ExprKind::BoolOp(_, items) => items.iter().all(ok),
        ExprKind::IfExp { cond, then, orelse } => ok(cond) && ok(then) && ok(orelse),
        ExprKind::Call { func, args, kwargs } => {
            matches!(&func.kind, ExprKind::Name(f) if matches!(f.as_str(), "min" | "max" | "abs" | "tdiv" | "tmod"))
                && kwargs.is_empty()
                && args.iter().all(ok)
        }
        _ => false,
    }
}

impl Expander<'_> {
    /// Records the bundle version of `[elt for var in range(…)]`, whose range gives `values`
    /// and whose unrolled elements are `items`, if it qualifies.
    pub(super) fn vectorise_range(&mut self, var: &str, elt: &Expr, values: &[Expr], items: &[Expr]) {
        let n = items.len();
        if std::env::var_os("TICKY_NO_VECTORISE").is_some() {
            return;
        }
        if n < 2 || n > MAX_MEM || !mentions(elt, var) || !elementwise(elt, var) || has_call(elt, self.fns) {
            return;
        }
        let computed = items.iter().filter(|x| self.fold(x).is_none() && !matches!(x.kind, ExprKind::Name(_))).count();
        if computed < MIN_COMPUTED {
            return;
        }
        let (Some(start), Some(second)) = (self.fold(&values[0]), self.fold(&values[1])) else { return };
        let (start, step) = (start as i64, second as i64 - start as i64);
        let span = elt.span;
        let mut banks = Vec::new();
        for (off, nb) in bank_ranges(n) {
            let id = self.fresh();
            let (sn, vn) = (format!("#s{id}.s"), format!("#v{id}.v"));
            // Element `off + k` is `start + step·(off + k)`, and `v = k + 1`.
            let c = (start + step * (off as i64 - 1)) as i32 as i64;
            let mut k = name(&vn, span);
            if step != 1 {
                k = bin(BinOp::Mul, k, int(step, span), span);
            }
            if c != 0 {
                k = bin(BinOp::Add, k, int(c, span), span);
            }
            // Expanding the element must not add statements (they'd run even if unused).
            let mut scratch = Vec::new();
            self.aliases.push(HashMap::from([(var.to_string(), k)]));
            let value = self.expr_scalar(elt, &mut scratch);
            self.aliases.pop();
            let Ok(value) = value else { return };
            if !scratch.is_empty() {
                return;
            }
            let Some(value) = self.truncating(&value) else { return };
            let target = Expr { kind: ExprKind::Tuple(vec![name(&sn, span), name(&vn, span)]), span };
            let comp = Expr {
                kind: ExprKind::DictComp {
                    key: Box::new(name(&sn, span)),
                    value: Box::new(value),
                    target: Box::new(target),
                    iter: Box::new(method_call(call("#aidx", vec![int(nb as i64, span)], span), "items", span)),
                    conds: vec![],
                },
                span,
            };
            banks.push(call("#vec", vec![comp, call("#arr", items[off..off + nb].to_vec(), span)], span));
        }
        let signal_array = arithmetic_on(elt, var).is_some_and(|n| n >= MIN_OPS);
        self.vectorised.push(Vectorised { key: format!("{items:?}"), banks, signal_array });
    }

    /// The recorded bundle version of these elements, if any.
    pub(super) fn vectorised(&self, items: &[Expr]) -> Option<&Vectorised> {
        if self.vectorised.is_empty() {
            return None;
        }
        let key = format!("{items:?}");
        self.vectorised.iter().find(|v| v.key == key)
    }

    /// The bundle version of these elements' banks, if recorded.
    pub(super) fn vectorised_banks(&self, items: &[Expr]) -> Option<Vec<Expr>> {
        self.vectorised(items).map(|v| v.banks.clone())
    }

    /// Forward a pure range producer into its adjacent sole reduction. Re-evaluating
    /// random/selector/user calls, or crossing any intervening statement, is forbidden:
    /// the original array denotes a snapshot. The normal assignment is still emitted.
    pub(super) fn forward_range_reduction(&self, producer: &Stmt, consumer: &Stmt) -> Option<Stmt> {
        let StmtKind::Assign { targets, value } = &producer.kind else { return None };
        let [Expr { kind: ExprKind::Name(n), .. }] = targets.as_slice() else { return None };
        if self.reads.get(n) != Some(&1) { return None; }
        let ExprKind::ListComp { elt, iter, conds, .. } = &value.kind else { return None };
        if !is_range(iter) || !conds.is_empty() { return None; }
        fn pure(e: &Expr) -> bool {
            match &e.kind {
                ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Name(_) => true,
                ExprKind::Unary(_, x) | ExprKind::Not(x) => pure(x),
                ExprKind::Binary(_, a, b) => pure(a) && pure(b),
                ExprKind::Compare(a, xs) => pure(a) && xs.iter().all(|(_, b)| pure(b)),
                ExprKind::BoolOp(_, xs) => xs.iter().all(pure),
                ExprKind::IfExp { cond, then, orelse } => pure(cond) && pure(then) && pure(orelse),
                ExprKind::Call { func, args, kwargs } => matches!(&func.kind, ExprKind::Name(f) if matches!(f.as_str(), "min" | "max" | "abs" | "tdiv" | "tmod"))
                    && kwargs.is_empty() && args.iter().all(pure),
                _ => false,
            }
        }
        if !pure(elt) { return None; }
        let StmtKind::Assign { targets: dest, value: reduction } = &consumer.kind else { return None };
        if !matches!(dest.as_slice(), [Expr { kind: ExprKind::Name(d), .. }] if d != n) { return None; }
        let ExprKind::Call { func, args, kwargs } = &reduction.kind else { return None };
        if !matches!(&func.kind, ExprKind::Name(f) if matches!(f.as_str(), "sum" | "min" | "max"))
            || !kwargs.is_empty() || !matches!(args.as_slice(), [Expr { kind: ExprKind::Name(a), .. }] if a == n) {
            return None;
        }
        let reduction = Expr { kind: ExprKind::Call { func: func.clone(), args: vec![value.clone()], kwargs: vec![] }, span: reduction.span };
        Some(Stmt { kind: StmtKind::Assign { targets: dest.clone(), value: reduction }, span: consumer.span })
    }

    /// Choose a representation for the whole producer/reduction region. Strip each
    /// bank's local choice: a cheaper bank is not necessarily a cheaper reduction.
    /// The scalar fallback retains the original element expressions and their checks.
    pub(super) fn vectorised_reduction(&self, f: &str, items: &[Expr], scalar: Expr, span: Span) -> Expr {
        let Some(v) = self.vectorised(items) else { return scalar };
        let mut parts = Vec::new();
        for (bank, (_, nb)) in v.banks.iter().zip(bank_ranges(items.len())) {
            let ExprKind::Call { args, .. } = &bank.kind else { unreachable!() };
            let b = args[0].clone();
            let part = match f {
                "sum" => method_call(b, "total", span),
                "min" | "max" => call(if f == "min" { "#amin" } else { "#amax" }, vec![b, int(nb as i64, span)], span),
                _ => unreachable!(),
            };
            parts.push(part);
        }
        let vector = parts.into_iter().reduce(|a, b| match f {
            "sum" => bin(BinOp::Add, a, b, span),
            "min" | "max" => call(f, vec![a, b], span),
            _ => unreachable!(),
        }).unwrap();
        call("#vec", vec![vector, scalar], span)
    }

    /// An expanded element expression as a bundle comprehension's value: Python's floor `//`
    /// and `%` by a constant `c` written with truncating `tdiv`/`tmod` (`tmod(tmod(a, c) + c,
    /// c)`; `tdiv(a, c)` minus 1 where the remainder's sign differs from `c`'s), exact with
    /// wrapping for |c| < 2^30. `None` if a comprehension can't compute it per signal.
    fn truncating(&self, e: &Expr) -> Option<Expr> {
        let span = e.span;
        let t = |x: &Expr| self.truncating(x);
        let kind = match &e.kind {
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Name(_) => return Some(e.clone()),
            ExprKind::Unary(op, a) => ExprKind::Unary(*op, Box::new(t(a)?)),
            ExprKind::Not(a) => ExprKind::Not(Box::new(t(a)?)),
            ExprKind::Binary(op @ (BinOp::FloorDiv | BinOp::Mod), a, b) => {
                let c = self.fold(b)?;
                if c == 0 || c.unsigned_abs() >= 1 << 30 {
                    return None;
                }
                let a = t(a)?;
                let k = int(c as i64, span);
                return Some(match (op, c) {
                    (BinOp::Mod, 1 | -1) => int(0, span),
                    (BinOp::FloorDiv, 1) => a,
                    (BinOp::FloorDiv, -1) => Expr { kind: ExprKind::Unary(UnOp::Neg, Box::new(a)), span },
                    (BinOp::Mod, _) => {
                        let r = call("tmod", vec![a, k.clone()], span);
                        call("tmod", vec![bin(BinOp::Add, r, k.clone(), span), k], span)
                    }
                    _ => {
                        let r = call("tmod", vec![a.clone(), k.clone()], span);
                        let wrong = compare(r, if c > 0 { CmpOp::Lt } else { CmpOp::Gt }, int(0, span), span);
                        let fix = if_exp(wrong, int(1, span), int(0, span), span);
                        bin(BinOp::Sub, call("tdiv", vec![a, k], span), fix, span)
                    }
                });
            }
            ExprKind::Binary(BinOp::Pow | BinOp::Div, ..) => return None,
            ExprKind::Binary(op, a, b) => ExprKind::Binary(*op, Box::new(t(a)?), Box::new(t(b)?)),
            ExprKind::Compare(a, rest) if rest.len() == 1 && !matches!(rest[0].0, CmpOp::In | CmpOp::NotIn) => {
                ExprKind::Compare(Box::new(t(a)?), vec![(rest[0].0, t(&rest[0].1)?)])
            }
            ExprKind::BoolOp(op, xs) => ExprKind::BoolOp(*op, xs.iter().map(t).collect::<Option<_>>()?),
            ExprKind::IfExp { cond, then, orelse } => {
                ExprKind::IfExp { cond: Box::new(t(cond)?), then: Box::new(t(then)?), orelse: Box::new(t(orelse)?) }
            }
            ExprKind::Call { func, args, kwargs }
                if kwargs.is_empty() && matches!(&func.kind, ExprKind::Name(f) if matches!(f.as_str(), "min" | "max" | "abs" | "tdiv" | "tmod")) =>
            {
                ExprKind::Call { func: func.clone(), args: args.iter().map(t).collect::<Option<_>>()?, kwargs: vec![] }
            }
            _ => return None,
        };
        Some(Expr { kind, span })
    }
}
