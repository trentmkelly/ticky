//! Source-to-source expansion, run before analysis:
//!
//! * **Functions are inlined.** Each call becomes a `Block` holding parameter assignments and
//!   the body, with locals renamed `f.<call>.<name>`; `return` assigns the result slots and
//!   exits the block. Calls inside expressions are hoisted into statements in evaluation
//!   order; `and`/`or`/`x if c else y` containing calls become real `if`s so short-circuiting
//!   is kept.
//! * **Arrays become scalars.** An array `xs` of length N is the variables `xs[0]` …
//!   `xs[N-1]`. Constant indexes name an element directly; a runtime index reads through a
//!   select and writes through one conditional assignment per element.
//! * **Comprehensions** over constant ranges or arrays become list literals.
//! * In `every` blocks, `for` loops are unrolled (their ranges must be constant).
//!
//! Python's dynamic typing is approximated by *shapes*: each variable is a scalar or an array
//! of a fixed length, fixed by its first assignment.

use std::collections::{BTreeMap, HashMap, HashSet};

use ticky_syntax::ast::{BinOp, BoolOp, CmpOp, Expr, ExprKind, Module, Param, Stmt, StmtKind, UnOp};
use ticky_syntax::{Diag, Span};

use crate::program::eval_const;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Shape {
    Scalar,
    Array(usize),
}

/// The value of an expanded expression.
#[derive(Clone, Debug)]
enum Val {
    /// A call to a function that returns nothing.
    None,
    Scalar(Expr),
    Array(Vec<Expr>),
    Tuple(Vec<Val>),
}

#[derive(Clone, Debug, PartialEq)]
enum RetShape {
    Scalar,
    Array(usize),
    Tuple(Vec<Shape>),
}

pub struct FnDef {
    pub name: String,
    pub params: Vec<Param>,
    pub body: Vec<Stmt>,
    pub span: Span,
    locals: HashSet<String>,
}

struct Frame {
    prefix: String,
    locals: HashSet<String>,
    exit: usize,
    ret: Option<RetShape>,
    name: String,
}

#[derive(Clone, Copy)]
enum Loop {
    /// A real loop (`break`/`continue` stay as they are).
    Real,
    /// An unrolled loop: `break` and `continue` exit these labelled blocks.
    Unrolled { brk: usize, cont: usize },
}

/// Largest array the compiler accepts (every element is a register).
const MAX_ARRAY: usize = 256;
/// Largest number of iterations an unrolled loop may have.
const MAX_UNROLL: usize = 1024;

pub struct Expander<'a> {
    fns: &'a HashMap<String, FnDef>,
    consts: &'a HashMap<String, crate::ir::Cv>,
    shapes: HashMap<String, Shape>,
    frames: Vec<Frame>,
    aliases: Vec<HashMap<String, Expr>>,
    loops: Vec<Loop>,
    stack: Vec<String>,
    /// Inside an `every` block: loops are unrolled, `while`/`wait` are errors.
    every: bool,
    next_id: usize,
    pub calls: BTreeMap<String, usize>,
    /// Functions compiled once and called as subroutines from sequential code (those with
    /// loops or waits); everything else is inlined.
    subs: HashSet<String>,
    /// Expanded subroutine bodies: exit label, body and result shape.
    sub_bodies: BTreeMap<String, (usize, Vec<Stmt>, Option<RetShape>)>,
}

fn name(n: &str, span: Span) -> Expr {
    Expr { kind: ExprKind::Name(n.to_string()), span }
}

fn int(v: i64, span: Span) -> Expr {
    Expr { kind: ExprKind::Int(v), span }
}

fn stmt(kind: StmtKind, span: Span) -> Stmt {
    Stmt { kind, span }
}

fn assign(n: &str, value: Expr, span: Span) -> Stmt {
    stmt(StmtKind::Assign { targets: vec![name(n, span)], value }, span)
}

fn element(base: &str, k: usize) -> String {
    format!("{base}[{k}]")
}

fn is_literal(e: &Expr) -> bool {
    matches!(e.kind, ExprKind::Int(_) | ExprKind::Bool(_))
        || matches!(&e.kind, ExprKind::Unary(UnOp::Neg, x) if matches!(x.kind, ExprKind::Int(_)))
}

/// Names assigned anywhere in a body (including loop targets), not descending into `def`s.
fn assigned(body: &[Stmt], out: &mut HashSet<String>) {
    fn target(e: &Expr, out: &mut HashSet<String>) {
        match &e.kind {
            ExprKind::Name(n) => {
                out.insert(n.clone());
            }
            ExprKind::Tuple(items) | ExprKind::List(items) => items.iter().for_each(|i| target(i, out)),
            // `xs[i] = …` modifies xs; it doesn't make xs local by itself (Python agrees).
            _ => {}
        }
    }
    for s in body {
        match &s.kind {
            StmtKind::Assign { targets, .. } => targets.iter().for_each(|t| target(t, out)),
            StmtKind::AugAssign { target: t, .. } | StmtKind::AnnAssign { target: t, .. } => target(t, out),
            StmtKind::For { target: t, body, .. } => {
                target(t, out);
                assigned(body, out);
            }
            StmtKind::If { body, orelse, .. } => {
                assigned(body, out);
                assigned(orelse, out);
            }
            StmtKind::While { body, .. } => assigned(body, out),
            _ => {}
        }
    }
}

fn globals_of(body: &[Stmt], out: &mut HashSet<String>) {
    for s in body {
        match &s.kind {
            StmtKind::Global(names) => out.extend(names.iter().cloned()),
            StmtKind::If { body, orelse, .. } => {
                globals_of(body, out);
                globals_of(orelse, out);
            }
            StmtKind::While { body, .. } | StmtKind::For { body, .. } => globals_of(body, out),
            _ => {}
        }
    }
}

impl FnDef {
    pub fn new(s: &Stmt) -> Option<FnDef> {
        let StmtKind::Def { name, params, body } = &s.kind else { return None };
        let mut locals = HashSet::new();
        assigned(body, &mut locals);
        let mut globals = HashSet::new();
        globals_of(body, &mut globals);
        locals.retain(|n| !globals.contains(n));
        locals.extend(params.iter().map(|p| p.name.clone()));
        Some(FnDef { name: name.clone(), params: params.clone(), body: body.clone(), span: s.span, locals })
    }
}

/// Whether an expression calls a user function (directly or inside a comprehension).
fn has_call(e: &Expr, fns: &HashMap<String, FnDef>) -> bool {
    let mut found = false;
    visit(e, &mut |x| {
        if let ExprKind::Call { func, .. } = &x.kind {
            if matches!(&func.kind, ExprKind::Name(n) if fns.contains_key(n)) {
                found = true;
            }
        }
    });
    found
}

fn visit(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    f(e);
    match &e.kind {
        ExprKind::Unary(_, a) | ExprKind::Not(a) | ExprKind::Attr(a, _) => visit(a, f),
        ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
            visit(a, f);
            visit(b, f);
        }
        ExprKind::Compare(a, rest) => {
            visit(a, f);
            rest.iter().for_each(|(_, x)| visit(x, f));
        }
        ExprKind::BoolOp(_, items) | ExprKind::Tuple(items) | ExprKind::List(items) => items.iter().for_each(|x| visit(x, f)),
        ExprKind::IfExp { cond, then, orelse } => {
            visit(cond, f);
            visit(then, f);
            visit(orelse, f);
        }
        ExprKind::Call { func, args, kwargs } => {
            visit(func, f);
            args.iter().for_each(|x| visit(x, f));
            kwargs.iter().for_each(|(_, x)| visit(x, f));
        }
        ExprKind::ListComp { elt, iter, conds, .. } => {
            visit(elt, f);
            visit(iter, f);
            conds.iter().for_each(|x| visit(x, f));
        }
        ExprKind::Dict(items) => items.iter().for_each(|(k, v)| {
            visit(k, f);
            visit(v, f);
        }),
        ExprKind::DictComp { key, value, iter, conds, .. } => {
            visit(key, f);
            visit(value, f);
            visit(iter, f);
            conds.iter().for_each(|x| visit(x, f));
        }
        ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Str(_) | ExprKind::Name(_) => {}
    }
}

impl<'a> Expander<'a> {
    pub fn new(fns: &'a HashMap<String, FnDef>, consts: &'a HashMap<String, crate::ir::Cv>, shapes: HashMap<String, Shape>) -> Self {
        Expander {
            fns,
            consts,
            shapes,
            frames: Vec::new(),
            aliases: Vec::new(),
            loops: Vec::new(),
            stack: Vec::new(),
            every: false,
            next_id: 0,
            calls: BTreeMap::new(),
            subs: HashSet::new(),
            sub_bodies: BTreeMap::new(),
        }
    }

    pub fn shapes(&self) -> &HashMap<String, Shape> {
        &self.shapes
    }

    fn fresh(&mut self) -> usize {
        self.next_id += 1;
        self.next_id
    }

    fn temp(&mut self) -> String {
        format!("#t{}", self.fresh())
    }

    fn resolve(&self, n: &str) -> String {
        match self.frames.last() {
            Some(f) if f.locals.contains(n) => format!("{}{n}", f.prefix),
            _ => n.to_string(),
        }
    }

    fn alias(&self, n: &str) -> Option<Expr> {
        self.aliases.iter().rev().find_map(|m| m.get(n).cloned())
    }

    fn shape(&self, resolved: &str) -> Shape {
        self.shapes.get(resolved).copied().unwrap_or(Shape::Scalar)
    }

    fn set_shape(&mut self, resolved: &str, s: Shape, span: Span) -> Result<(), Diag> {
        match self.shapes.get(resolved) {
            Some(old) if *old != s => {
                let show = |s: Shape| match s {
                    Shape::Scalar => "a single value".to_string(),
                    Shape::Array(n) => format!("an array of {n}"),
                };
                Err(Diag::error(span, format!("`{}` is {} here but {} elsewhere", display(resolved), show(s), show(*old)))
                    .with_help("a variable keeps one shape: a single value, or an array of one length"))
            }
            _ => {
                self.shapes.insert(resolved.to_string(), s);
                Ok(())
            }
        }
    }

    fn fold(&self, e: &Expr) -> Option<i32> {
        eval_const(e, self.consts, &[]).ok().and_then(|c| c.int())
    }

    fn scalar(&self, v: Val, span: Span) -> Result<Expr, Diag> {
        match v {
            Val::Scalar(e) => Ok(e),
            Val::Array(es) => Err(Diag::error(span, format!("expected a single value, but this is an array of {}", es.len()))
                .with_help("index it, e.g. `xs[0]`, or reduce it with `sum`, `min` or `max`")),
            Val::Tuple(_) => Err(Diag::error(span, "expected a single value, but this is a tuple")),
            Val::None => Err(Diag::error(span, "this function doesn't return a value")),
        }
    }

    // ---------------------------------------------------------------- expressions

    fn expr(&mut self, e: &Expr, out: &mut Vec<Stmt>) -> Result<Val, Diag> {
        let span = e.span;
        let rebuild = |kind: ExprKind| Val::Scalar(Expr { kind, span });
        Ok(match &e.kind {
            ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Str(_) => Val::Scalar(e.clone()),
            ExprKind::Name(n) => {
                if let Some(a) = self.alias(n) {
                    return Ok(Val::Scalar(Expr { span, ..a }));
                }
                let r = self.resolve(n);
                match self.shape(&r) {
                    Shape::Scalar => Val::Scalar(name(&r, span)),
                    Shape::Array(k) => Val::Array((0..k).map(|i| name(&element(&r, i), span)).collect()),
                }
            }
            ExprKind::Unary(op, a) => {
                let a = self.expr_scalar(a, out)?;
                rebuild(ExprKind::Unary(*op, Box::new(a)))
            }
            ExprKind::Not(a) => {
                let a = self.expr_scalar(a, out)?;
                rebuild(ExprKind::Not(Box::new(a)))
            }
            ExprKind::Binary(op, a, b) => {
                let (va, vb) = (self.expr(a, out)?, self.expr(b, out)?);
                match (op, va, vb) {
                    (BinOp::Add, Val::Array(x), Val::Array(y)) => Val::Array(x.into_iter().chain(y).collect()),
                    (BinOp::Mul, Val::Array(x), Val::Scalar(k)) | (BinOp::Mul, Val::Scalar(k), Val::Array(x)) => {
                        let n = self.fold(&k).ok_or_else(|| Diag::error(k.span, "an array can only be repeated a constant number of times"))?;
                        let n = n.max(0) as usize;
                        if x.len() * n > MAX_ARRAY {
                            return Err(Diag::error(span, format!("arrays are limited to {MAX_ARRAY} elements")));
                        }
                        Val::Array((0..n).flat_map(|_| x.iter().cloned()).collect())
                    }
                    (_, va, vb) => {
                        let (a, b) = (self.scalar(va, a.span)?, self.scalar(vb, b.span)?);
                        rebuild(ExprKind::Binary(*op, Box::new(a), Box::new(b)))
                    }
                }
            }
            ExprKind::Compare(first, rest) => {
                // `x in xs` / `x not in xs` over an array.
                if let [(op @ (CmpOp::In | CmpOp::NotIn), rhs)] = rest.as_slice() {
                    let x = self.expr_scalar(first, out)?;
                    let items = match self.expr(rhs, out)? {
                        Val::Array(items) => items,
                        // A bundle: `sig in b`, checked when lowering.
                        Val::Scalar(b) => return Ok(rebuild(ExprKind::Compare(Box::new(x), vec![(*op, b)]))),
                        _ => return Err(Diag::error(rhs.span, "`in` needs an array or a bundle on the right")),
                    };
                    let tmp = self.bind(x, out);
                    let (cmp, bop) = if *op == CmpOp::In { (CmpOp::Eq, BoolOp::Or) } else { (CmpOp::Ne, BoolOp::And) };
                    if items.is_empty() {
                        return Ok(rebuild(ExprKind::Bool(*op == CmpOp::NotIn)));
                    }
                    let tests: Vec<Expr> = items
                        .into_iter()
                        .map(|it| Expr { kind: ExprKind::Compare(Box::new(tmp.clone()), vec![(cmp, it)]), span })
                        .collect();
                    return Ok(rebuild(ExprKind::BoolOp(bop, tests)));
                }
                let f = self.expr_scalar(first, out)?;
                let mut r = Vec::new();
                for (op, x) in rest {
                    r.push((*op, self.expr_scalar(x, out)?));
                }
                rebuild(ExprKind::Compare(Box::new(f), r))
            }
            ExprKind::BoolOp(op, items) => {
                if items[1..].iter().any(|i| has_call(i, self.fns)) {
                    // Keep short-circuiting: later operands only run when needed.
                    let t = self.temp();
                    let first = self.expr_scalar(&items[0], out)?;
                    out.push(assign(&t, first, span));
                    self.short_circuit(*op, &t, &items[1..], out)?;
                    return Ok(Val::Scalar(name(&t, span)));
                }
                let mut v = Vec::new();
                for i in items {
                    v.push(self.expr_scalar(i, out)?);
                }
                rebuild(ExprKind::BoolOp(*op, v))
            }
            ExprKind::IfExp { cond, then, orelse } => {
                let c = self.expr_scalar(cond, out)?;
                if has_call(then, self.fns) || has_call(orelse, self.fns) {
                    let t = self.temp();
                    let (mut a, mut b) = (Vec::new(), Vec::new());
                    let va = self.expr_scalar(then, &mut a)?;
                    a.push(assign(&t, va, span));
                    let vb = self.expr_scalar(orelse, &mut b)?;
                    b.push(assign(&t, vb, span));
                    out.push(stmt(StmtKind::If { cond: c, body: a, orelse: b }, span));
                    return Ok(Val::Scalar(name(&t, span)));
                }
                match (self.expr(then, out)?, self.expr(orelse, out)?) {
                    (Val::Array(x), Val::Array(y)) if x.len() == y.len() => {
                        let c = self.bind(c, out);
                        Val::Array(
                            x.into_iter()
                                .zip(y)
                                .map(|(p, q)| Expr {
                                    kind: ExprKind::IfExp { cond: Box::new(c.clone()), then: Box::new(p), orelse: Box::new(q) },
                                    span,
                                })
                                .collect(),
                        )
                    }
                    (va, vb) => {
                        let (a, b) = (self.scalar(va, then.span)?, self.scalar(vb, orelse.span)?);
                        rebuild(ExprKind::IfExp { cond: Box::new(c), then: Box::new(a), orelse: Box::new(b) })
                    }
                }
            }
            ExprKind::Call { func, args, kwargs } => {
                if let ExprKind::Attr(base, m) = &func.kind {
                    // A bundle method: `b.total()`, `b.items()`, …
                    let b = self.expr_scalar(base, out)?;
                    let mut a = Vec::new();
                    for x in args {
                        a.push(self.expr_scalar(x, out)?);
                    }
                    let mut kw = Vec::new();
                    for (k, x) in kwargs {
                        kw.push((k.clone(), self.expr_scalar(x, out)?));
                    }
                    let f = Expr { kind: ExprKind::Attr(Box::new(b), m.clone()), span: func.span };
                    return Ok(rebuild(ExprKind::Call { func: Box::new(f), args: a, kwargs: kw }));
                }
                let ExprKind::Name(fname) = &func.kind else {
                    return Err(Diag::error(func.span, "only named functions can be called"));
                };
                if self.alias(fname).is_none() && self.fns.contains_key(fname.as_str()) && !self.is_local(fname) {
                    return self.call(fname, args, kwargs, span, out);
                }
                self.builtin(fname, args, kwargs, span, out)?
            }
            ExprKind::Index(base, idx) => {
                let items = match self.expr(base, out)? {
                    Val::Array(items) => items,
                    // A bundle: `b[sig]`, checked when lowering.
                    Val::Scalar(b) => {
                        let i = self.expr_scalar(idx, out)?;
                        return Ok(rebuild(ExprKind::Index(Box::new(b), Box::new(i))));
                    }
                    _ => return Err(Diag::error(base.span, "only arrays and bundles can be indexed")),
                };
                let i = self.expr_scalar(idx, out)?;
                match self.fold(&i) {
                    Some(k) => {
                        let n = items.len() as i64;
                        let k = k as i64;
                        let k = if k < 0 { k + n } else { k };
                        if !(0..n).contains(&k) {
                            return Err(Diag::error(idx.span, format!("index {k} is out of range for an array of {n}")));
                        }
                        Val::Scalar(items[k as usize].clone())
                    }
                    None => {
                        // Runtime index: a select over all elements (0 if out of range).
                        let mut args = vec![i];
                        args.extend(items);
                        rebuild(ExprKind::Call { func: Box::new(name("#select", span)), args, kwargs: vec![] })
                    }
                }
            }
            ExprKind::Attr(base, n) => {
                let b = self.expr_scalar(base, out)?;
                rebuild(ExprKind::Attr(Box::new(b), n.clone()))
            }
            ExprKind::Dict(items) => {
                let mut v = Vec::new();
                for (k, x) in items {
                    v.push((self.expr_scalar(k, out)?, self.expr_scalar(x, out)?));
                }
                rebuild(ExprKind::Dict(v))
            }
            ExprKind::DictComp { key, value, target, iter, conds } => {
                // The comprehension's own names (`s`, `v`) get fresh names so they never
                // clash with variables or function locals.
                let id = self.fresh();
                let mut own = HashMap::new();
                let mut new_target = Vec::new();
                if let ExprKind::Tuple(ts) = &target.kind {
                    for (i, t) in ts.iter().enumerate() {
                        if let ExprKind::Name(n) = &t.kind {
                            let fresh = format!("#{}{id}.{n}", if i == 0 { 's' } else { 'v' });
                            own.insert(n.clone(), name(&fresh, t.span));
                            new_target.push(name(&fresh, t.span));
                        }
                    }
                }
                if new_target.len() != 2 {
                    return Err(Diag::error(target.span, "a bundle comprehension needs two names: `for s, v in b.items()`"));
                }
                for x in std::iter::once(&**value).chain(conds.iter()) {
                    if has_call(x, self.fns) {
                        return Err(Diag::error(x.span, "functions can't be called inside a bundle comprehension")
                            .with_help("it runs on every signal at once, in a few combinators; compute the function's result first"));
                    }
                }
                let iter = self.expr_scalar(iter, out)?;
                self.aliases.push(own);
                let r = (|| -> Result<(Expr, Expr, Vec<Expr>), Diag> {
                    let k = self.expr_scalar(key, out)?;
                    let v = self.expr_scalar(value, out)?;
                    let mut cs = Vec::new();
                    for c in conds {
                        cs.push(self.expr_scalar(c, out)?);
                    }
                    Ok((k, v, cs))
                })();
                self.aliases.pop();
                let (k, v, cs) = r?;
                let target = Expr { kind: ExprKind::Tuple(new_target), span: target.span };
                rebuild(ExprKind::DictComp {
                    key: Box::new(k),
                    value: Box::new(v),
                    target: Box::new(target),
                    iter: Box::new(iter),
                    conds: cs,
                })
            }
            ExprKind::Tuple(items) => {
                let mut v = Vec::new();
                for i in items {
                    v.push(self.expr(i, out)?);
                }
                Val::Tuple(v)
            }
            ExprKind::List(items) => {
                let mut v = Vec::new();
                for i in items {
                    v.push(self.expr_scalar(i, out)?);
                }
                if v.len() > MAX_ARRAY {
                    return Err(Diag::error(span, format!("arrays are limited to {MAX_ARRAY} elements")));
                }
                Val::Array(v)
            }
            ExprKind::ListComp { elt, target, iter, conds } => {
                let ExprKind::Name(t) = &target.kind else {
                    return Err(Diag::error(target.span, "the comprehension variable must be a single name"));
                };
                let values = self.iteration_values(iter, out)?;
                let mut items = Vec::new();
                for v in values {
                    self.aliases.push(HashMap::from([(t.clone(), v)]));
                    let mut keep = true;
                    for c in conds {
                        let c = self.expr_scalar(c, out)?;
                        match self.fold(&c) {
                            Some(k) => keep &= k != 0,
                            None => {
                                self.aliases.pop();
                                return Err(Diag::error(c.span, "comprehension filters must be constant")
                                    .with_help("arrays have a fixed length, so the filter must be decidable when compiling"));
                            }
                        }
                    }
                    if keep {
                        let x = self.expr_scalar(elt, out);
                        self.aliases.pop();
                        items.push(x?);
                    } else {
                        self.aliases.pop();
                    }
                }
                Val::Array(items)
            }
        })
    }

    fn expr_scalar(&mut self, e: &Expr, out: &mut Vec<Stmt>) -> Result<Expr, Diag> {
        let v = self.expr(e, out)?;
        self.scalar(v, e.span)
    }

    fn is_local(&self, n: &str) -> bool {
        self.frames.last().is_some_and(|f| f.locals.contains(n))
    }

    /// A simple expression as-is; anything else is evaluated once into a temporary.
    fn bind(&mut self, e: Expr, out: &mut Vec<Stmt>) -> Expr {
        if matches!(e.kind, ExprKind::Name(_) | ExprKind::Int(_) | ExprKind::Bool(_)) {
            return e;
        }
        let t = self.temp();
        let span = e.span;
        out.push(assign(&t, e, span));
        name(&t, span)
    }

    fn short_circuit(&mut self, op: BoolOp, t: &str, rest: &[Expr], out: &mut Vec<Stmt>) -> Result<(), Diag> {
        let Some((next, more)) = rest.split_first() else { return Ok(()) };
        let span = next.span;
        let mut body = Vec::new();
        let v = self.expr_scalar(next, &mut body)?;
        body.push(assign(t, v, span));
        self.short_circuit(op, t, more, &mut body)?;
        let test = match op {
            BoolOp::And => name(t, span),
            BoolOp::Or => Expr { kind: ExprKind::Not(Box::new(name(t, span))), span },
        };
        out.push(stmt(StmtKind::If { cond: test, body, orelse: vec![] }, span));
        Ok(())
    }

    /// The values a `for`/comprehension iterates over: a constant range or an array.
    fn iteration_values(&mut self, iter: &Expr, out: &mut Vec<Stmt>) -> Result<Vec<Expr>, Diag> {
        if let ExprKind::Call { func, args, kwargs } = &iter.kind {
            if matches!(&func.kind, ExprKind::Name(n) if n == "range") && kwargs.is_empty() && (1..=3).contains(&args.len()) {
                let mut v = Vec::new();
                for a in args {
                    let x = self.expr_scalar(a, out)?;
                    v.push(self.fold(&x).ok_or_else(|| {
                        Diag::error(a.span, "this range must be constant here").with_help(
                            "loops inside `every` blocks and comprehensions are unrolled, so their ranges must be known when compiling",
                        )
                    })? as i64);
                }
                let (start, end, step) = match v.as_slice() {
                    [e] => (0, *e, 1),
                    [s, e] => (*s, *e, 1),
                    [s, e, st] => (*s, *e, *st),
                    _ => unreachable!(),
                };
                if step == 0 {
                    return Err(Diag::error(iter.span, "the range step can't be 0"));
                }
                let mut vals = Vec::new();
                let mut k = start;
                while (step > 0 && k < end) || (step < 0 && k > end) {
                    vals.push(int(k, iter.span));
                    k += step;
                    if vals.len() > MAX_UNROLL {
                        return Err(Diag::error(iter.span, format!("too many iterations to unroll (more than {MAX_UNROLL})")));
                    }
                }
                return Ok(vals);
            }
        }
        match self.expr(iter, out)? {
            Val::Array(items) => {
                // Elements might change during the loop; iterate over a snapshot.
                Ok(items.into_iter().map(|e| self.bind(e, out)).collect())
            }
            _ => Err(Diag::error(iter.span, "can only iterate over `range(…)` or an array")),
        }
    }

    fn builtin(&mut self, f: &str, args: &[Expr], kwargs: &[(String, Expr)], span: Span, out: &mut Vec<Stmt>) -> Result<Val, Diag> {
        let mut vals = Vec::new();
        for a in args {
            vals.push(self.expr(a, out)?);
        }
        let mut kw = Vec::new();
        for (k, a) in kwargs {
            kw.push((k.clone(), self.expr_scalar(a, out)?));
        }
        let call = |name_: &str, args: Vec<Expr>| Expr {
            kind: ExprKind::Call { func: Box::new(name(name_, span)), args, kwargs: vec![] },
            span,
        };
        // Balanced reduction tree, so depth grows with log(n).
        fn tree(items: Vec<Expr>, join: &dyn Fn(Expr, Expr) -> Expr) -> Expr {
            if items.len() == 1 {
                return items.into_iter().next().unwrap();
            }
            let mut items = items;
            let right = items.split_off(items.len() / 2);
            join(tree(items, join), tree(right, join))
        }
        match (f, vals.as_slice()) {
            ("len", [Val::Array(xs)]) => return Ok(Val::Scalar(int(xs.len() as i64, span))),
            ("len", [Val::Scalar(_)]) => {} // a bundle
            ("len", _) => return Err(Diag::error(span, "`len` needs an array or a bundle")),
            ("sum", [Val::Array(xs)]) => {
                if xs.is_empty() {
                    return Ok(Val::Scalar(int(0, span)));
                }
                let add = |a: Expr, b: Expr| Expr { kind: ExprKind::Binary(BinOp::Add, Box::new(a), Box::new(b)), span };
                return Ok(Val::Scalar(tree(xs.clone(), &add)));
            }
            ("any" | "all", [Val::Array(xs)]) => {
                if xs.is_empty() {
                    return Ok(Val::Scalar(Expr { kind: ExprKind::Bool(f == "all"), span }));
                }
                let op = if f == "any" { BoolOp::Or } else { BoolOp::And };
                let tests = xs.iter().map(|x| call("bool", vec![x.clone()])).collect();
                return Ok(Val::Scalar(Expr { kind: ExprKind::BoolOp(op, tests), span }));
            }
            ("min" | "max", [Val::Array(xs)]) if !xs.is_empty() => {
                return Ok(Val::Scalar(tree(xs.clone(), &|a, b| call(f, vec![a, b]))));
            }
            ("min" | "max", [Val::Array(_)]) => return Err(Diag::error(span, format!("`{f}` of an empty array"))),
            ("sorted" | "reversed" | "enumerate" | "zip", _) => {
                return Err(Diag::error(span, format!("`{f}` isn't supported yet")));
            }
            _ => {}
        }
        let mut scalars = Vec::new();
        for (v, a) in vals.into_iter().zip(args) {
            scalars.push(self.scalar(v, a.span)?);
        }
        if (f == "min" || f == "max") && scalars.len() > 2 {
            return Ok(Val::Scalar(tree(scalars, &|a, b| call(f, vec![a, b]))));
        }
        Ok(Val::Scalar(Expr {
            kind: ExprKind::Call {
                func: Box::new(name(f, span)),
                args: scalars,
                kwargs: kw,
            },
            span,
        }))
    }

    fn call(&mut self, f: &str, args: &[Expr], kwargs: &[(String, Expr)], span: Span, out: &mut Vec<Stmt>) -> Result<Val, Diag> {
        let def = &self.fns[f];
        if self.stack.iter().any(|s| s == f) {
            return Err(Diag::error(span, format!("`{f}` calls itself (recursion isn't supported yet)"))
                .with_help("every call is expanded in place, so a function can't call itself, directly or indirectly"));
        }
        // Bind arguments, evaluated left to right in the caller.
        let mut bound: Vec<Option<Val>> = vec![None; def.params.len()];
        if args.len() > def.params.len() {
            return Err(Diag::error(span, format!("`{f}` takes {} argument(s), got {}", def.params.len(), args.len())));
        }
        for (i, a) in args.iter().enumerate() {
            bound[i] = Some(self.expr(a, out)?);
        }
        for (k, a) in kwargs {
            let Some(i) = def.params.iter().position(|p| &p.name == k) else {
                return Err(Diag::error(a.span, format!("`{f}` has no parameter `{k}`")));
            };
            if bound[i].is_some() {
                return Err(Diag::error(a.span, format!("`{k}` is given twice")));
            }
            bound[i] = Some(self.expr(a, out)?);
        }
        let params = def.params.clone();
        for (i, p) in params.iter().enumerate() {
            if bound[i].is_none() {
                match &p.default {
                    Some(d) => bound[i] = Some(self.expr(d, out)?),
                    None => return Err(Diag::error(span, format!("`{f}` needs an argument for `{}`", p.name))),
                }
            }
        }

        if self.subs.contains(f) && !self.every {
            return self.sub_call(f, &params, bound, span, out);
        }
        let id = self.fresh();
        let exit = self.fresh();
        *self.calls.entry(f.to_string()).or_default() += 1;
        if std::env::var_os("TICKY_TIMING").is_some() {
            let total: usize = self.calls.values().sum();
            if total.is_multiple_of(50) {
                eprintln!("[expand] {total} calls inlined, depth {}", self.stack.len());
            }
        }
        let def = &self.fns[f];
        self.frames.push(Frame { prefix: format!("{f}.{id}."), locals: def.locals.clone(), exit, ret: None, name: f.to_string() });
        self.stack.push(f.to_string());
        let saved_loops = std::mem::take(&mut self.loops);
        let saved_aliases = std::mem::take(&mut self.aliases);
        let body_src = def.body.clone();
        let result = (|| -> Result<Vec<Stmt>, Diag> {
            let mut body = Vec::new();
            for (p, v) in params.iter().zip(bound) {
                let target = name(&p.name, p.span);
                self.assign_to(&target, v.unwrap(), p.span, &mut body)?;
            }
            body.extend(self.stmts(&body_src)?);
            Ok(body)
        })();
        self.loops = saved_loops;
        self.aliases = saved_aliases;
        self.stack.pop();
        let frame = self.frames.pop().unwrap();
        let body = result?;
        out.push(stmt(StmtKind::Block { label: exit, body }, span));
        let slot = |s: &str| format!("{}#ret{s}", frame.prefix);
        Ok(match frame.ret {
            None => Val::None,
            Some(RetShape::Scalar) => Val::Scalar(name(&slot(""), span)),
            Some(RetShape::Array(n)) => Val::Array((0..n).map(|k| name(&element(&slot(""), k), span)).collect()),
            Some(RetShape::Tuple(shapes)) => Val::Tuple(
                shapes
                    .iter()
                    .enumerate()
                    .map(|(i, s)| match s {
                        Shape::Scalar => Val::Scalar(name(&slot(&i.to_string()), span)),
                        Shape::Array(n) => Val::Array((0..*n).map(|k| name(&element(&slot(&i.to_string()), k), span)).collect()),
                    })
                    .collect(),
            ),
        })
    }

    /// A call to a subroutine: assign its (shared) parameters, `Call`, then copy the result
    /// out before anything can call it again.
    fn sub_call(&mut self, f: &str, params: &[Param], bound: Vec<Option<Val>>, span: Span, out: &mut Vec<Stmt>) -> Result<Val, Diag> {
        for (p, v) in params.iter().zip(bound) {
            self.assign_to(&name(&format!("{f}.{}", p.name), p.span), v.unwrap(), p.span, out)?;
        }
        if !self.sub_bodies.contains_key(f) {
            let exit = self.fresh();
            let def = &self.fns[f];
            self.frames.push(Frame { prefix: format!("{f}."), locals: def.locals.clone(), exit, ret: None, name: f.to_string() });
            self.stack.push(f.to_string());
            let saved_loops = std::mem::take(&mut self.loops);
            let saved_aliases = std::mem::take(&mut self.aliases);
            let src = def.body.clone();
            let body = self.stmts(&src);
            self.loops = saved_loops;
            self.aliases = saved_aliases;
            self.stack.pop();
            let frame = self.frames.pop().unwrap();
            self.sub_bodies.insert(f.to_string(), (exit, body?, frame.ret));
        } else if self.stack.iter().any(|s| s == f) {
            return Err(Diag::error(span, format!("`{f}` calls itself (recursion isn't supported yet)")));
        }
        *self.calls.entry(f.to_string()).or_default() += 1;
        out.push(stmt(StmtKind::Call(f.to_string()), span));
        let ret = self.sub_bodies[f].2.clone();
        let slot = |s: &str| format!("{f}.#ret{s}");
        let copy = |this: &mut Self, shape: Shape, from: &str, out: &mut Vec<Stmt>| -> Result<Val, Diag> {
            let t = this.temp();
            let v = match shape {
                Shape::Scalar => Val::Scalar(name(from, span)),
                Shape::Array(n) => Val::Array((0..n).map(|k| name(&element(from, k), span)).collect()),
            };
            this.assign_to(&name(&t, span), v, span, out)?;
            this.expr(&name(&t, span), out)
        };
        Ok(match ret {
            None => Val::None,
            Some(RetShape::Scalar) => copy(self, Shape::Scalar, &slot(""), out)?,
            Some(RetShape::Array(n)) => copy(self, Shape::Array(n), &slot(""), out)?,
            Some(RetShape::Tuple(shapes)) => {
                let mut parts = Vec::new();
                for (i, sh) in shapes.into_iter().enumerate() {
                    parts.push(copy(self, sh, &slot(&i.to_string()), out)?);
                }
                Val::Tuple(parts)
            }
        })
    }

    // ---------------------------------------------------------------- assignment

    /// Assigns `v` to `target` (a name, an element, or a tuple of those).
    fn assign_to(&mut self, target: &Expr, v: Val, span: Span, out: &mut Vec<Stmt>) -> Result<(), Diag> {
        match &target.kind {
            ExprKind::Name(n) => {
                if self.alias(n).is_some() {
                    return Err(Diag::error(target.span, format!("can't assign to `{n}` here")));
                }
                let r = self.resolve(n);
                match v {
                    Val::Scalar(e) => {
                        self.set_shape(&r, Shape::Scalar, target.span)?;
                        out.push(assign(&r, e, span));
                    }
                    Val::Array(items) => {
                        self.set_shape(&r, Shape::Array(items.len()), target.span)?;
                        let names: Vec<String> = (0..items.len()).map(|k| element(&r, k)).collect();
                        self.parallel_assign(names, items, span, out);
                    }
                    Val::Tuple(_) => {
                        return Err(Diag::error(span, "can't store a tuple in one variable")
                            .with_help("unpack it instead, e.g. `a, b = …`"))
                    }
                    Val::None => return Err(Diag::error(span, "this function doesn't return a value")),
                }
            }
            ExprKind::Tuple(targets) | ExprKind::List(targets) => {
                let parts: Vec<Val> = match v {
                    Val::Tuple(p) => p,
                    Val::Array(items) => items.into_iter().map(Val::Scalar).collect(),
                    _ => return Err(Diag::error(span, "can only unpack a tuple or an array")),
                };
                if parts.len() != targets.len() {
                    return Err(Diag::error(span, format!("can't unpack {} value(s) into {} name(s)", parts.len(), targets.len())));
                }
                // Everything on the right is evaluated before anything is assigned.
                let mut names = Vec::new();
                let mut values = Vec::new();
                for (t, p) in targets.iter().zip(parts) {
                    match (&t.kind, p) {
                        (ExprKind::Name(_), Val::Array(items)) => {
                            let ExprKind::Name(n) = &t.kind else { unreachable!() };
                            let r = self.resolve(n);
                            self.set_shape(&r, Shape::Array(items.len()), t.span)?;
                            for (k, it) in items.into_iter().enumerate() {
                                names.push(element(&r, k));
                                values.push(it);
                            }
                        }
                        (ExprKind::Name(n), Val::Scalar(e)) => {
                            if self.alias(n).is_some() {
                                return Err(Diag::error(t.span, format!("can't assign to `{n}` here")));
                            }
                            let r = self.resolve(n);
                            self.set_shape(&r, Shape::Scalar, t.span)?;
                            names.push(r);
                            values.push(e);
                        }
                        (ExprKind::Index(base, idx), Val::Scalar(e)) => {
                            let (arr, len) = self.array_name(base)?;
                            let i = self.expr_scalar(idx, out)?;
                            let k = self.const_index(&i, len, idx.span, "in a multiple assignment")?;
                            names.push(element(&arr, k));
                            values.push(e);
                        }
                        _ => return Err(Diag::error(t.span, "can't assign this here")),
                    }
                }
                self.parallel_assign(names, values, span, out);
            }
            ExprKind::Index(base, idx) if self.is_bundle_name(base) => {
                // `b[k] = e` is `b = #bset(b, k, e)`: only that signal changes.
                let b = self.expr_scalar(base, out)?;
                let k = self.expr_scalar(idx, out)?;
                let e = self.scalar(v, span)?;
                let set = Expr { kind: ExprKind::Call { func: Box::new(name("#bset", span)), args: vec![b, k, e], kwargs: vec![] }, span };
                self.assign_to(base, Val::Scalar(set), span, out)?;
            }
            ExprKind::Index(base, idx) => {
                let (arr, len) = self.array_name(base)?;
                let i = self.expr_scalar(idx, out)?;
                let e = self.scalar(v, span)?;
                match self.fold(&i) {
                    Some(_) => {
                        let k = self.const_index(&i, len, idx.span, "")?;
                        out.push(assign(&element(&arr, k), e, span));
                    }
                    None => {
                        // Runtime index: each element takes the value if the index matches.
                        let i = self.bind(i, out);
                        let e = self.bind(e, out);
                        for k in 0..len {
                            let el = element(&arr, k);
                            let hit = Expr {
                                kind: ExprKind::Compare(Box::new(i.clone()), vec![(CmpOp::Eq, int(k as i64, span))]),
                                span,
                            };
                            out.push(stmt(StmtKind::If { cond: hit, body: vec![assign(&el, e.clone(), span)], orelse: vec![] }, span));
                        }
                    }
                }
            }
            _ => return Err(Diag::error(target.span, "can only assign to names and array elements")),
        }
        Ok(())
    }

    fn parallel_assign(&mut self, names: Vec<String>, values: Vec<Expr>, span: Span, out: &mut Vec<Stmt>) {
        if names.is_empty() {
            return;
        }
        // Constants can't depend on the targets, so separate assignments are equivalent (and
        // let the prologue treat them as initial values).
        let folded: Vec<Option<i32>> = values.iter().map(|v| self.fold(v)).collect();
        if names.len() > 1 && folded.iter().all(|f| f.is_some()) {
            for (n, k) in names.iter().zip(folded) {
                out.push(assign(n, int(k.unwrap() as i64, span), span));
            }
            return;
        }
        if names.len() == 1 || values.iter().all(is_literal) {
            for (n, v) in names.iter().zip(values) {
                out.push(assign(n, v, span));
            }
            return;
        }
        let targets = Expr { kind: ExprKind::Tuple(names.iter().map(|n| name(n, span)).collect()), span };
        let value = Expr { kind: ExprKind::Tuple(values), span };
        out.push(stmt(StmtKind::Assign { targets: vec![targets], value }, span));
    }

    /// A named single value (a bundle, when indexed): not an array.
    fn is_bundle_name(&self, base: &Expr) -> bool {
        match &base.kind {
            ExprKind::Name(n) => self.alias(n).is_none() && self.shape(&self.resolve(n)) == Shape::Scalar,
            _ => false,
        }
    }

    fn array_name(&self, base: &Expr) -> Result<(String, usize), Diag> {
        let ExprKind::Name(n) = &base.kind else {
            return Err(Diag::error(base.span, "can only assign to elements of a named array"));
        };
        let r = self.resolve(n);
        match self.shape(&r) {
            Shape::Array(len) => Ok((r, len)),
            Shape::Scalar => Err(Diag::error(base.span, format!("`{n}` isn't an array"))),
        }
    }

    fn const_index(&self, i: &Expr, len: usize, span: Span, ctx: &str) -> Result<usize, Diag> {
        let k = self.fold(i).ok_or_else(|| Diag::error(span, format!("the index must be constant {ctx}")))? as i64;
        let k = if k < 0 { k + len as i64 } else { k };
        if !(0..len as i64).contains(&k) {
            return Err(Diag::error(span, format!("index {k} is out of range for an array of {len}")));
        }
        Ok(k as usize)
    }

    // ---------------------------------------------------------------- statements

    pub fn every_block(&mut self, body: &[Stmt]) -> Result<Vec<Stmt>, Diag> {
        self.every = true;
        let r = self.stmts(body);
        self.every = false;
        r
    }

    pub fn stmts(&mut self, body: &[Stmt]) -> Result<Vec<Stmt>, Diag> {
        let mut out = Vec::new();
        for s in body {
            self.stmt(s, &mut out)?;
        }
        Ok(out)
    }

    fn stmt(&mut self, s: &Stmt, out: &mut Vec<Stmt>) -> Result<(), Diag> {
        let span = s.span;
        match &s.kind {
            StmtKind::Assign { targets, value } => {
                let v = self.expr(value, out)?;
                // `a = b = value`: evaluate once, then assign left to right.
                if targets.len() > 1 {
                    let first = &targets[0];
                    self.assign_to(first, v, span, out)?;
                    let again = self.expr(first, out)?;
                    for t in &targets[1..] {
                        self.assign_to(t, again.clone(), span, out)?;
                    }
                } else {
                    self.assign_to(&targets[0], v, span, out)?;
                }
            }
            StmtKind::AnnAssign { target, ann, value } => {
                let Some(value) = value else { return Ok(()) };
                let v = self.expr(value, out)?;
                match (&target.kind, &v) {
                    (ExprKind::Name(n), Val::Scalar(e)) => {
                        let r = self.resolve(n);
                        self.set_shape(&r, Shape::Scalar, target.span)?;
                        out.push(stmt(StmtKind::AnnAssign { target: name(&r, target.span), ann: ann.clone(), value: Some(e.clone()) }, span));
                    }
                    _ => self.assign_to(target, v, span, out)?,
                }
            }
            StmtKind::AugAssign { target, op, value } => {
                if let ExprKind::Index(base, _) = &target.kind {
                    if self.is_bundle_name(base) {
                        // `b[k] += e` is `b[k] = b[k] + e`.
                        let rhs = Expr { kind: ExprKind::Binary(*op, Box::new(target.clone()), Box::new(value.clone())), span };
                        return self.stmt(&stmt(StmtKind::Assign { targets: vec![target.clone()], value: rhs }, span), out);
                    }
                }
                let v = self.expr_scalar(value, out)?;
                match &target.kind {
                    ExprKind::Name(n) => {
                        let r = self.resolve(n);
                        if let Shape::Array(_) = self.shape(&r) {
                            return Err(Diag::error(target.span, format!("`{n}` is an array; `{}=` needs a single value", op.symbol())));
                        }
                        out.push(stmt(StmtKind::AugAssign { target: name(&r, target.span), op: *op, value: v }, span));
                    }
                    ExprKind::Index(base, idx) => {
                        let (arr, len) = self.array_name(base)?;
                        let i = self.expr_scalar(idx, out)?;
                        match self.fold(&i) {
                            Some(_) => {
                                let k = self.const_index(&i, len, idx.span, "")?;
                                out.push(stmt(StmtKind::AugAssign { target: name(&element(&arr, k), target.span), op: *op, value: v }, span));
                            }
                            None => {
                                let i = self.bind(i, out);
                                let v = self.bind(v, out);
                                for k in 0..len {
                                    let el = element(&arr, k);
                                    let hit = Expr {
                                        kind: ExprKind::Compare(Box::new(i.clone()), vec![(CmpOp::Eq, int(k as i64, span))]),
                                        span,
                                    };
                                    let upd = stmt(StmtKind::AugAssign { target: name(&el, span), op: *op, value: v.clone() }, span);
                                    out.push(stmt(StmtKind::If { cond: hit, body: vec![upd], orelse: vec![] }, span));
                                }
                            }
                        }
                    }
                    _ => return Err(Diag::error(target.span, "can only assign to names and array elements")),
                }
            }
            StmtKind::Expr(e) => match self.expr(e, out)? {
                Val::None => {}
                Val::Scalar(x) if matches!(e.kind, ExprKind::Call { .. }) && !matches!(x.kind, ExprKind::Call { .. }) => {}
                Val::Scalar(x) => out.push(stmt(StmtKind::Expr(x), span)),
                _ => {}
            },
            StmtKind::If { cond, body, orelse } => {
                let c = self.expr_scalar(cond, out)?;
                let (b, o) = (self.stmts(body)?, self.stmts(orelse)?);
                out.push(stmt(StmtKind::If { cond: c, body: b, orelse: o }, span));
            }
            StmtKind::While { cond, body } => {
                if self.every {
                    return Err(Diag::error(span, "`while` can't be used in an `every` block")
                        .with_help("`every` blocks already repeat; use `for` over a constant range, or write the loop in the main program"));
                }
                self.loops.push(Loop::Real);
                let r = (|| -> Result<(), Diag> {
                    if has_call(cond, self.fns) {
                        // Re-evaluate the condition (and its calls) at the top of every iteration.
                        let mut b = Vec::new();
                        let c = self.expr_scalar(cond, &mut b)?;
                        let not_c = Expr { kind: ExprKind::Not(Box::new(c)), span };
                        b.push(stmt(StmtKind::If { cond: not_c, body: vec![stmt(StmtKind::Break, span)], orelse: vec![] }, span));
                        b.extend(self.stmts(body)?);
                        out.push(stmt(StmtKind::While { cond: Expr { kind: ExprKind::Bool(true), span }, body: b }, span));
                    } else {
                        let c = self.expr_scalar(cond, out)?;
                        let b = self.stmts(body)?;
                        out.push(stmt(StmtKind::While { cond: c, body: b }, span));
                    }
                    Ok(())
                })();
                self.loops.pop();
                r?;
            }
            StmtKind::For { target, iter, body } => self.for_loop(target, iter, body, span, out)?,
            StmtKind::Break | StmtKind::Continue => {
                let is_break = matches!(s.kind, StmtKind::Break);
                match self.loops.last() {
                    None => return Err(Diag::error(span, format!("`{}` outside a loop", if is_break { "break" } else { "continue" }))),
                    Some(Loop::Real) => out.push(s.clone()),
                    Some(Loop::Unrolled { brk, cont }) => out.push(stmt(StmtKind::Exit(if is_break { *brk } else { *cont }), span)),
                }
            }
            StmtKind::Return(v) => {
                let Some(frame) = self.frames.last() else {
                    return Err(Diag::error(span, "`return` outside a function"));
                };
                let (prefix, exit, fname) = (frame.prefix.clone(), frame.exit, frame.name.clone());
                if let Some(v) = v {
                    let val = self.expr(v, out)?;
                    let shape = match &val {
                        Val::Scalar(_) => RetShape::Scalar,
                        Val::Array(xs) => RetShape::Array(xs.len()),
                        Val::Tuple(parts) => RetShape::Tuple(
                            parts
                                .iter()
                                .map(|p| match p {
                                    Val::Array(xs) => Ok(Shape::Array(xs.len())),
                                    Val::Scalar(_) => Ok(Shape::Scalar),
                                    _ => Err(Diag::error(v.span, "can't return nested tuples")),
                                })
                                .collect::<Result<_, _>>()?,
                        ),
                        Val::None => return Err(Diag::error(v.span, "this function doesn't return a value")),
                    };
                    let frame = self.frames.last_mut().unwrap();
                    match &frame.ret {
                        Some(old) if *old != shape => {
                            return Err(Diag::error(v.span, format!("`{fname}` returns different kinds of values on different paths")))
                        }
                        _ => frame.ret = Some(shape),
                    }
                    // Assign the result slots (outside the function's local scope).
                    let slot = |s: &str| format!("{prefix}#ret{s}");
                    let saved = self.frames.pop();
                    let r = match val {
                        Val::Tuple(parts) => {
                            let targets = Expr {
                                kind: ExprKind::Tuple((0..parts.len()).map(|i| name(&slot(&i.to_string()), span)).collect()),
                                span,
                            };
                            self.assign_to(&targets, Val::Tuple(parts), span, out)
                        }
                        val => self.assign_to(&name(&slot(""), span), val, span, out),
                    };
                    self.frames.push(saved.unwrap());
                    r?;
                }
                out.push(stmt(StmtKind::Exit(exit), span));
            }
            StmtKind::Global(_) => {
                if self.frames.is_empty() {
                    return Err(Diag::error(span, "`global` is only meaningful inside a function"));
                }
            }
            StmtKind::WaitUntil(c) => {
                if self.every {
                    return Err(Diag::error(span, "`wait` can't be used in an `every` block"));
                }
                let mut pre = Vec::new();
                let c = self.expr_scalar(c, &mut pre)?;
                if !pre.is_empty() {
                    return Err(Diag::error(span, "`wait until` conditions can't call functions")
                        .with_help("loop instead: `while not f(): wait 1`"));
                }
                out.push(stmt(StmtKind::WaitUntil(c), span));
            }
            StmtKind::WaitTicks(n) => {
                if self.every {
                    return Err(Diag::error(span, "`wait` can't be used in an `every` block"));
                }
                let n = self.expr_scalar(n, out)?;
                out.push(stmt(StmtKind::WaitTicks(n), span));
            }
            StmtKind::Def { .. } => return Err(Diag::error(span, "functions must be defined at the top level of the file")),
            _ => out.push(s.clone()),
        }
        Ok(())
    }

    fn for_loop(&mut self, target: &Expr, iter: &Expr, body: &[Stmt], span: Span, out: &mut Vec<Stmt>) -> Result<(), Diag> {
        let ExprKind::Name(t) = &target.kind else {
            return Err(Diag::error(target.span, "the loop variable must be a single name"));
        };
        let is_range = matches!(&iter.kind, ExprKind::Call { func, .. } if matches!(&func.kind, ExprKind::Name(n) if n == "range"));
        if self.every {
            // Unroll: one labelled block per iteration inside one for the whole loop.
            let values = self.iteration_values(iter, out)?;
            let mut assigned_in_body = HashSet::new();
            assigned(body, &mut assigned_in_body);
            let substitute = !assigned_in_body.contains(t);
            let brk = self.fresh();
            let mut iterations = Vec::new();
            for v in values {
                let cont = self.fresh();
                let mut it = Vec::new();
                self.assign_to(target, Val::Scalar(v.clone()), span, &mut it)?;
                if substitute {
                    self.aliases.push(HashMap::from([(t.clone(), v)]));
                }
                self.loops.push(Loop::Unrolled { brk, cont });
                let b = self.stmts(body);
                self.loops.pop();
                if substitute {
                    self.aliases.pop();
                }
                it.extend(b?);
                iterations.push(stmt(StmtKind::Block { label: cont, body: it }, span));
            }
            out.push(stmt(StmtKind::Block { label: brk, body: iterations }, span));
            return Ok(());
        }
        if is_range {
            let ExprKind::Call { func, args, kwargs } = &iter.kind else { unreachable!() };
            let mut a = Vec::new();
            for x in args {
                a.push(self.expr_scalar(x, out)?);
            }
            let r = self.resolve(t);
            self.set_shape(&r, Shape::Scalar, target.span)?;
            self.loops.push(Loop::Real);
            let b = self.stmts(body);
            self.loops.pop();
            let iter = Expr { kind: ExprKind::Call { func: func.clone(), args: a, kwargs: kwargs.clone() }, span: iter.span };
            out.push(stmt(StmtKind::For { target: name(&r, target.span), iter, body: b? }, span));
            return Ok(());
        }
        // `for x in xs` in sequential code: loop over indexes, reading through a select.
        let Val::Array(items) = self.expr(iter, out)? else {
            return Err(Diag::error(iter.span, "can only iterate over `range(…)` or an array"));
        };
        let items: Vec<Expr> = items.into_iter().map(|e| self.bind(e, out)).collect();
        let idx = self.temp();
        let mut args = vec![name(&idx, span)];
        args.extend(items.iter().cloned());
        let pick = Expr { kind: ExprKind::Call { func: Box::new(name("#select", span)), args, kwargs: vec![] }, span };
        let mut b = Vec::new();
        self.assign_to(target, Val::Scalar(pick), span, &mut b)?;
        self.loops.push(Loop::Real);
        let rest = self.stmts(body);
        self.loops.pop();
        b.extend(rest?);
        let range = Expr {
            kind: ExprKind::Call { func: Box::new(name("range", span)), args: vec![int(items.len() as i64, span)], kwargs: vec![] },
            span,
        };
        out.push(stmt(StmtKind::For { target: name(&idx, span), iter: range, body: b }, span));
        Ok(())
    }
}

/// An internal name for messages, quoted: `x` → "`x`", `f.3.x` → "`x` in `f`".
pub fn quoted(n: &str) -> String {
    let d = display(n);
    if d.starts_with('`') || d.starts_with("the ") || d.starts_with("a ") {
        d
    } else {
        format!("`{d}`")
    }
}

/// A readable form of an internal name: `f.3.x` → `x` in `f`, `#t5` → a temporary.
pub fn display(n: &str) -> String {
    if n.starts_with("#t") {
        return "a temporary value".into();
    }
    // A comprehension's own names: `#s4.s` → `s`.
    if n.starts_with("#s") || n.starts_with("#v") {
        if let Some((_, own)) = n.split_once('.') {
            return own.to_string();
        }
    }
    if let Some((f, rest)) = n.split_once('.') {
        // `f.3.x` (an inlined call's local) or `f.x` (a subroutine's local).
        let local = rest.split_once('.').map_or(rest, |(_, l)| l);
        if let Some(r) = local.strip_prefix("#ret") {
            return format!("the return value of `{f}`{r}");
        }
        return format!("`{}` in `{f}`", display(local).trim_matches('`'));
    }
    n.to_string()
}

// ---------------------------------------------------------------- flattening

fn contains_exit(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match &s.kind {
        StmtKind::Exit(_) => true,
        StmtKind::If { body, orelse, .. } => contains_exit(body) || contains_exit(orelse),
        StmtKind::Block { body, .. } | StmtKind::While { body, .. } | StmtKind::For { body, .. } => contains_exit(body),
        _ => false,
    })
}

/// Removes `Block`/`Exit` from straight-line code by moving the code that follows an `if`
/// into whichever of its branches can reach it. Exits must target blocks inside `code`.
pub fn flatten(code: Vec<Stmt>, budget: &mut usize) -> Result<Vec<Stmt>, Diag> {
    flat(code, &HashMap::new(), budget)
}

fn flat(code: Vec<Stmt>, exits: &HashMap<usize, Vec<Stmt>>, budget: &mut usize) -> Result<Vec<Stmt>, Diag> {
    let mut out = Vec::new();
    let mut code = code.into_iter();
    while let Some(s) = code.next() {
        if *budget == 0 {
            return Err(Diag::error(s.span, "too much branching to expand here (try fewer early `return`s or `break`s)"));
        }
        *budget -= 1;
        match s.kind {
            StmtKind::Exit(l) => {
                let rest = exits.get(&l).cloned().ok_or_else(|| Diag::error(s.span, "internal error: exit to an unknown block"))?;
                out.extend(flat(rest, exits, budget)?);
                return Ok(out);
            }
            StmtKind::Block { label, body } => {
                let rest: Vec<Stmt> = code.collect();
                if !contains_exit(&body) {
                    let mut all = body;
                    all.extend(rest);
                    out.extend(flat(all, exits, budget)?);
                    return Ok(out);
                }
                let mut ex = exits.clone();
                ex.insert(label, rest.clone());
                let mut all = body;
                all.extend(rest);
                out.extend(flat(all, &ex, budget)?);
                return Ok(out);
            }
            StmtKind::If { cond, body, orelse } if contains_exit(&body) || contains_exit(&orelse) => {
                let rest: Vec<Stmt> = code.collect();
                let a: Vec<Stmt> = body.into_iter().chain(rest.iter().cloned()).collect();
                let b: Vec<Stmt> = orelse.into_iter().chain(rest).collect();
                let (a, b) = (flat(a, exits, budget)?, flat(b, exits, budget)?);
                out.push(stmt(StmtKind::If { cond, body: a, orelse: b }, s.span));
                return Ok(out);
            }
            StmtKind::If { cond, body, orelse } => {
                let (a, b) = (flat(body, exits, budget)?, flat(orelse, exits, budget)?);
                out.push(stmt(StmtKind::If { cond, body: a, orelse: b }, s.span));
            }
            kind => out.push(Stmt { kind, span: s.span }),
        }
    }
    Ok(out)
}

/// Whether a statement can be flattened in place: no loops or waits inside, and every exit
/// targets a block inside it.
pub fn flattenable(s: &Stmt) -> bool {
    fn walk(stmts: &[Stmt], labels: &mut Vec<usize>) -> bool {
        stmts.iter().all(|s| match &s.kind {
            StmtKind::While { .. } | StmtKind::For { .. } | StmtKind::WaitUntil(_) | StmtKind::WaitTicks(_) => false,
            StmtKind::Break | StmtKind::Continue | StmtKind::Call(_) => false,
            StmtKind::Exit(l) => labels.contains(l),
            StmtKind::If { body, orelse, .. } => walk(body, labels) && walk(orelse, labels),
            StmtKind::Block { label, body } => {
                labels.push(*label);
                let ok = walk(body, labels);
                labels.pop();
                ok
            }
            _ => true,
        })
    }
    walk(std::slice::from_ref(s), &mut Vec::new())
}

// ---------------------------------------------------------------- module

/// Expands a module: inlines every function call, turns arrays into scalars and unrolls
/// loops in `every` blocks. Returns the expanded module and call counts per function.
/// Call counts per function, and which functions became subroutines.
pub type CallInfo = (BTreeMap<String, usize>, std::collections::BTreeSet<String>);

pub fn expand_module(m: &Module) -> Result<(Module, CallInfo), Vec<Diag>> {
    let mut fns = HashMap::new();
    let mut errs = Vec::new();
    for s in &m.body {
        if let Some(f) = FnDef::new(s) {
            if fns.contains_key(&f.name) {
                errs.push(Diag::error(s.span, format!("function `{}` is defined twice", f.name)));
            }
            fns.insert(f.name.clone(), f);
        }
    }
    if !errs.is_empty() {
        return Err(errs);
    }
    let consts = module_consts(m, &fns);
    // Two passes: the first discovers the shape of every module-level variable (which may be
    // assigned after it is used), the second expands with that knowledge. Ports are scalars.
    let mut shapes: HashMap<String, Shape> = m
        .body
        .iter()
        .filter_map(|s| match &s.kind {
            StmtKind::Port { name, .. } => Some((name.clone(), Shape::Scalar)),
            _ => None,
        })
        .collect();
    for round in 0..2 {
        let mut ex = Expander::new(&fns, &consts, shapes.clone());
        ex.subs = sequential_fns(&fns);
        let mut body = Vec::new();
        let mut errs = Vec::new();
        let mut main = Vec::new();
        for s in &m.body {
            let r: Result<(), Diag> = (|| {
                match &s.kind {
                    StmtKind::Def { .. } => {}
                    StmtKind::Port { .. } | StmtKind::Test { .. } => body.push(s.clone()),
                    StmtKind::Every { period, body: b } => {
                        let expanded = ex.every_block(b)?;
                        let mut budget = 200_000;
                        let flat = flatten(expanded, &mut budget)?;
                        body.push(stmt(StmtKind::Every { period: period.clone(), body: flat }, s.span));
                    }
                    _ => {
                        ex.stmt(s, &mut main)?;
                    }
                }
                Ok(())
            })();
            if let Err(d) = r {
                errs.push(d);
            }
        }
        if round == 0 {
            shapes = ex.shapes().clone();
            continue;
        }
        if !errs.is_empty() {
            return Err(errs);
        }
        // Main statements go at the end (declarations keep their own order), then subroutines.
        body.extend(main);
        let sub_names = ex.sub_bodies.keys().cloned().collect();
        for (name, (label, b, _)) in std::mem::take(&mut ex.sub_bodies) {
            body.push(stmt(StmtKind::Sub { name, label, body: b }, Span::default()));
        }
        return Ok((Module { body }, (ex.calls, sub_names)));
    }
    unreachable!()
}

/// Functions with loops or waits (directly or through the functions they call): these become
/// subroutines when called from sequential code.
fn sequential_fns(fns: &HashMap<String, FnDef>) -> HashSet<String> {
    fn has_loop(body: &[Stmt]) -> bool {
        body.iter().any(|s| match &s.kind {
            StmtKind::While { .. } | StmtKind::For { .. } | StmtKind::WaitUntil(_) | StmtKind::WaitTicks(_) => true,
            StmtKind::If { body, orelse, .. } => has_loop(body) || has_loop(orelse),
            _ => false,
        })
    }
    fn calls(body: &[Stmt], fns: &HashMap<String, FnDef>) -> HashSet<String> {
        let mut out = HashSet::new();
        fn exprs_of(s: &Stmt, f: &mut dyn FnMut(&Expr)) {
            match &s.kind {
                StmtKind::Assign { targets, value } => {
                    targets.iter().for_each(|t| visit(t, f));
                    visit(value, f);
                }
                StmtKind::AugAssign { target, value, .. } => {
                    visit(target, f);
                    visit(value, f);
                }
                StmtKind::AnnAssign { value: Some(v), .. } | StmtKind::Expr(v) | StmtKind::WaitUntil(v) | StmtKind::WaitTicks(v) => visit(v, f),
                StmtKind::Return(Some(v)) => visit(v, f),
                StmtKind::If { cond, body, orelse } => {
                    visit(cond, f);
                    body.iter().chain(orelse).for_each(|s| exprs_of(s, f));
                }
                StmtKind::While { cond, body } => {
                    visit(cond, f);
                    body.iter().for_each(|s| exprs_of(s, f));
                }
                StmtKind::For { iter, body, .. } => {
                    visit(iter, f);
                    body.iter().for_each(|s| exprs_of(s, f));
                }
                _ => {}
            }
        }
        for s in body {
            exprs_of(s, &mut |e| {
                if let ExprKind::Call { func, .. } = &e.kind {
                    if let ExprKind::Name(n) = &func.kind {
                        if fns.contains_key(n) {
                            out.insert(n.clone());
                        }
                    }
                }
            });
        }
        out
    }
    let mut seq: HashSet<String> = fns.iter().filter(|(_, d)| has_loop(&d.body)).map(|(n, _)| n.clone()).collect();
    loop {
        let more: Vec<String> = fns
            .iter()
            .filter(|(n, d)| !seq.contains(*n) && calls(&d.body, fns).iter().any(|c| seq.contains(c)))
            .map(|(n, _)| n.clone())
            .collect();
        if more.is_empty() {
            return seq;
        }
        seq.extend(more);
    }
}

/// Top-level names assigned once from a constant and never anywhere else (approximately what
/// the analysis will treat as constants), for folding indexes and ranges.
fn module_consts(m: &Module, fns: &HashMap<String, FnDef>) -> HashMap<String, crate::ir::Cv> {
    let mut counts: HashMap<String, usize> = HashMap::new();
    let count = |counts: &mut HashMap<String, usize>, body: &[Stmt]| {
        let mut set = HashSet::new();
        assigned(body, &mut set);
        for n in set {
            *counts.entry(n).or_default() += 1;
        }
    };
    for s in &m.body {
        match &s.kind {
            StmtKind::Every { body, .. } => count(&mut counts, body),
            StmtKind::Def { body, .. } => {
                let mut g = HashSet::new();
                globals_of(body, &mut g);
                let mut a = HashSet::new();
                assigned(body, &mut a);
                for n in a.intersection(&g) {
                    *counts.entry(n.clone()).or_default() += 1;
                }
            }
            StmtKind::Port { .. } | StmtKind::Test { .. } => {}
            _ => count(&mut counts, std::slice::from_ref(s)),
        }
    }
    let mut consts = HashMap::new();
    for s in &m.body {
        if let StmtKind::Assign { targets, value } = &s.kind {
            if let [Expr { kind: ExprKind::Name(n), .. }] = targets.as_slice() {
                if counts.get(n) == Some(&1) && !fns.contains_key(n) {
                    if let Ok(v) = eval_const(value, &consts, &[]) {
                        consts.insert(n.clone(), v);
                    }
                }
            }
        }
    }
    consts
}
