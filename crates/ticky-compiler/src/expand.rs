//! Source-to-source expansion, run before analysis:
//!
//! * **Functions are inlined.** Each call becomes a `Block` holding parameter assignments and
//!   the body, with locals renamed `f.<call>.<name>`; `return` assigns the result slots and
//!   exits the block. Calls inside expressions are hoisted into statements in evaluation
//!   order; `and`/`or`/`x if c else y` containing calls become real `if`s so short-circuiting
//!   is kept.
//! * **Arrays become scalars or signal arrays.** An array indexed only by constants (a
//!   *register array*) is the variables `xs[0]` … `xs[N-1]`. An array indexed at runtime, or
//!   too long for registers, is a *signal array*: bundles `xs#0`, `xs#1`, … (banks of up to
//!   one signal table each) with element `k` on signal `Graph::slot(k)`, read and written by
//!   the `#a…` builtins. Which arrays are which is found by expanding again until it settles.
//! * **Comprehensions** over constant ranges or arrays become list literals.
//! * In `every` blocks, `for` loops are unrolled (their ranges must be constant).
//!
//! Python's dynamic typing is approximated by *shapes*: each variable is a scalar or an array
//! of a fixed length, fixed by its first assignment.

use std::collections::{BTreeMap, HashMap, HashSet};

use ticky_syntax::ast::{BinOp, BoolOp, CmpOp, Expr, ExprKind, Module, Param, Stmt, StmtKind, UnOp};
use ticky_syntax::{Diag, Span};

use crate::program::eval_const;

mod specialize;
mod vectorize;

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Shape {
    Scalar,
    Array(usize),
    /// A signal array of this length.
    Mem(usize),
}

/// The value of an expanded expression.
#[derive(Clone, Debug)]
enum Val {
    /// A call to a function that returns nothing.
    None,
    Scalar(Expr),
    Array(Vec<Expr>),
    /// A signal array: its banks (bundle expressions) and its length.
    Mem(Vec<Expr>, usize),
    Tuple(Vec<Val>),
}

#[derive(Clone, Debug, PartialEq)]
enum RetShape {
    Scalar,
    Array(usize),
    Mem(usize),
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

/// Largest register array (every element is a register); longer arrays are signal arrays.
const MAX_ARRAY: usize = 256;
/// Largest array of any kind.
const MAX_MEM: usize = 4096;
/// Return shapes are compatible when they only differ in array representation.
fn same_shape(a: &RetShape, b: &RetShape) -> bool {
    let len = |s: &Shape| match s {
        Shape::Scalar => None,
        Shape::Array(n) | Shape::Mem(n) => Some(*n),
    };
    match (a, b) {
        (RetShape::Scalar, RetShape::Scalar) => true,
        (RetShape::Array(x) | RetShape::Mem(x), RetShape::Array(y) | RetShape::Mem(y)) => x == y,
        (RetShape::Tuple(x), RetShape::Tuple(y)) => x.len() == y.len() && x.iter().zip(y).all(|(p, q)| len(p) == len(q)),
        _ => false,
    }
}

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
    constant_leaves: HashSet<String>,
    constant_cache: HashMap<(String, Vec<i32>), Option<i32>>,
    outline_costs: HashMap<String, usize>,
    outline_site: bool,
    isolated_calls: HashSet<usize>,
    unroll_sites: HashSet<usize>,
    observed: HashSet<String>,
    next_id: usize,
    pub calls: BTreeMap<String, usize>,
    /// Functions compiled once and called as subroutines from sequential code (those with
    /// loops or waits); everything else is inlined.
    subs: HashSet<String>,
    /// Call sites of each subroutine (by [`Expander::sub_key`]) expanded in this round.
    sub_sites: HashMap<String, usize>,
    /// Subroutines with a single call site (found in the previous round): inlined there
    /// instead, saving the return-address register, the call and the return.
    inline_once: HashSet<String>,
    /// Reads of each name in the whole module (see [`count_reads`]).
    reads: HashMap<String, usize>,
    /// Functions that change module variables (directly or through calls): a call to one
    /// can change values read earlier in the same expression.
    impure: HashSet<String>,
    /// Expanded subroutine bodies: exit label, body and result shape.
    sub_bodies: BTreeMap<String, (usize, Vec<Stmt>, Option<RetShape>)>,
    /// Arrays (by [`mem_key`]) that are signal arrays in this round.
    mem_keys: HashSet<String>,
    /// Arrays found to need a signal array (indexed at runtime, or given one).
    found_mem: HashSet<String>,
    /// Inside a `process`: its name (it gets its own copies of subroutines).
    proc: Option<String>,
    /// Names of arrays written element by element anywhere (see [`element_writes`]).
    elem_written: HashSet<String>,
    /// Range comprehensions' elements (by their `Debug` text) with their bundle version
    /// (see [`vectorize`]).
    vectorised: Vec<vectorize::Vectorised>,
}

/// Elements per bank of a signal array: one signal table.
pub fn bank_size() -> usize {
    ticky_factorio::SignalTable::base().array_signals().len()
}

/// `(offset, length)` of each bank of an `n`-element signal array.
fn bank_ranges(n: usize) -> Vec<(usize, usize)> {
    let s = bank_size();
    (0..n.div_ceil(s)).map(|b| (b * s, s.min(n - b * s))).collect()
}

fn bank_name(r: &str, b: usize) -> String {
    format!("{r}#{b}")
}

/// The value of signal array variable `r`.
fn mem_names(r: &str, n: usize, span: Span) -> Val {
    Val::Mem((0..bank_ranges(n).len()).map(|b| name(&bank_name(r, b), span)).collect(), n)
}

/// A name without the call numbers of inlined calls (`f.3.xs` → `f.xs`): the same for every
/// call and every expansion round.
fn mem_key(r: &str) -> String {
    r.split('.').filter(|p| p.is_empty() || !p.bytes().all(|c| c.is_ascii_digit())).collect::<Vec<_>>().join(".")
}

fn call(f: &str, args: Vec<Expr>, span: Span) -> Expr {
    Expr { kind: ExprKind::Call { func: Box::new(name(f, span)), args, kwargs: vec![] }, span }
}

fn method_call(base: Expr, m: &str, span: Span) -> Expr {
    let f = Expr { kind: ExprKind::Attr(Box::new(base), m.to_string()), span };
    Expr { kind: ExprKind::Call { func: Box::new(f), args: vec![], kwargs: vec![] }, span }
}

fn bin(op: BinOp, a: Expr, b: Expr, span: Span) -> Expr {
    Expr { kind: ExprKind::Binary(op, Box::new(a), Box::new(b)), span }
}

fn compare(a: Expr, op: CmpOp, b: Expr, span: Span) -> Expr {
    Expr { kind: ExprKind::Compare(Box::new(a), vec![(op, b)]), span }
}

fn if_exp(c: Expr, a: Expr, b: Expr, span: Span) -> Expr {
    Expr { kind: ExprKind::IfExp { cond: Box::new(c), then: Box::new(a), orelse: Box::new(b) }, span }
}

/// `i - off`.
fn minus(i: &Expr, off: usize, span: Span) -> Expr {
    if off == 0 {
        i.clone()
    } else {
        bin(BinOp::Sub, i.clone(), int(off as i64, span), span)
    }
}

/// Whether `e` mentions the name `var`.
fn mentions(e: &Expr, var: &str) -> bool {
    let mut found = false;
    visit(e, &mut |x| {
        if matches!(&x.kind, ExprKind::Name(n) if n == var) {
            found = true;
        }
    });
    found
}

/// Whether an element expression of `var` can run on all elements at once (bundle
/// operations), with the same result as element by element. Floor division and modulo
/// can't: per-signal arithmetic truncates.
fn per_element(e: &Expr, var: &str) -> bool {
    if !mentions(e, var) {
        return true;
    }
    let ok = |x: &Expr| per_element(x, var);
    match &e.kind {
        ExprKind::Name(_) => true,
        ExprKind::Unary(_, a) | ExprKind::Not(a) => ok(a),
        ExprKind::Binary(op, a, b) => !matches!(op, BinOp::Pow | BinOp::Div | BinOp::FloorDiv | BinOp::Mod) && ok(a) && ok(b),
        ExprKind::Compare(a, rest) => {
            rest.len() == 1 && !matches!(rest[0].0, CmpOp::In | CmpOp::NotIn) && ok(a) && ok(&rest[0].1)
        }
        ExprKind::BoolOp(_, items) => items.iter().all(ok),
        ExprKind::IfExp { cond, then, orelse } => ok(cond) && ok(then) && ok(orelse),
        ExprKind::Call { func, args, kwargs } => {
            matches!(&func.kind, ExprKind::Name(f) if matches!(f.as_str(), "min" | "max" | "abs"))
                && kwargs.is_empty()
                && args.iter().all(ok)
        }
        _ => false,
    }
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

fn is_range(e: &Expr) -> bool {
    matches!(&e.kind, ExprKind::Call { func, .. } if matches!(&func.kind, ExprKind::Name(n) if n == "range"))
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

/// How often each name is read in `body`, everywhere (functions, blocks, processes, tests).
/// Ports and `global` declarations count as reads: something outside the code sees them.
/// Plain assignment and loop targets don't count; `x += …` does.
fn count_reads(body: &[Stmt], out: &mut HashMap<String, usize>) {
    fn expr(e: &Expr, out: &mut HashMap<String, usize>) {
        visit(e, &mut |x| {
            if let ExprKind::Name(n) = &x.kind {
                *out.entry(n.clone()).or_default() += 1;
            }
        });
    }
    fn target(e: &Expr, out: &mut HashMap<String, usize>) {
        match &e.kind {
            ExprKind::Name(_) => {}
            ExprKind::Tuple(items) | ExprKind::List(items) => items.iter().for_each(|i| target(i, out)),
            _ => expr(e, out),
        }
    }
    for s in body {
        match &s.kind {
            StmtKind::Assign { targets, value } => {
                targets.iter().for_each(|t| target(t, out));
                expr(value, out);
            }
            StmtKind::AnnAssign { target: t, value, .. } => {
                target(t, out);
                value.iter().for_each(|v| expr(v, out));
            }
            StmtKind::AugAssign { target: t, value, .. } => {
                expr(t, out);
                expr(value, out);
            }
            StmtKind::Expr(e) | StmtKind::Assert(e) | StmtKind::WaitUntil(e) | StmtKind::WaitTicks(e) | StmtKind::Return(Some(e)) => expr(e, out),
            StmtKind::TestSet { value: e, .. } | StmtKind::TestRun { ticks: e } => expr(e, out),
            StmtKind::TestRunUntil { cond, max } => {
                expr(cond, out);
                expr(max, out);
            }
            StmtKind::Global(names) => names.iter().for_each(|n| *out.entry(n.clone()).or_default() += 1),
            StmtKind::Port { name, .. } => *out.entry(name.clone()).or_default() += 1,
            StmtKind::If { cond, body, orelse } => {
                expr(cond, out);
                count_reads(body, out);
                count_reads(orelse, out);
            }
            StmtKind::While { cond, body } => {
                expr(cond, out);
                count_reads(body, out);
            }
            StmtKind::For { target: t, iter, body } => {
                target(t, out);
                expr(iter, out);
                count_reads(body, out);
            }
            StmtKind::Every { period, body } => {
                period.iter().for_each(|p| expr(p, out));
                count_reads(body, out);
            }
            StmtKind::Def { body, .. } | StmtKind::Process { body, .. } | StmtKind::Test { body, .. } => count_reads(body, out),
            StmtKind::Block { body, .. } | StmtKind::Sub { body, .. } => count_reads(body, out),
            StmtKind::Return(None) | StmtKind::Pass | StmtKind::Break | StmtKind::Continue | StmtKind::Import(_) => {}
            StmtKind::Exit(_) | StmtKind::Call(_) => {}
        }
    }
}

/// Names (unresolved, in any scope) assigned element by element: `xs[i] = …`, `xs[i] += …`.
fn element_writes(body: &[Stmt], out: &mut HashSet<String>) {
    fn target(e: &Expr, out: &mut HashSet<String>) {
        match &e.kind {
            ExprKind::Index(base, _) => {
                if let ExprKind::Name(n) = &base.kind {
                    out.insert(n.clone());
                }
                target(base, out);
            }
            ExprKind::Tuple(items) | ExprKind::List(items) => items.iter().for_each(|i| target(i, out)),
            _ => {}
        }
    }
    for s in body {
        match &s.kind {
            StmtKind::Assign { targets, .. } => targets.iter().for_each(|t| target(t, out)),
            StmtKind::AnnAssign { target: t, .. } | StmtKind::AugAssign { target: t, .. } | StmtKind::For { target: t, .. } => target(t, out),
            _ => {}
        }
        match &s.kind {
            StmtKind::If { body, orelse, .. } => {
                element_writes(body, out);
                element_writes(orelse, out);
            }
            StmtKind::While { body, .. } | StmtKind::For { body, .. } | StmtKind::Every { body, .. } => element_writes(body, out),
            StmtKind::Def { body, .. } | StmtKind::Process { body, .. } | StmtKind::Test { body, .. } => element_writes(body, out),
            StmtKind::Block { body, .. } | StmtKind::Sub { body, .. } => element_writes(body, out),
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

pub(crate) fn visit(e: &Expr, f: &mut dyn FnMut(&Expr)) {
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
            constant_leaves: HashSet::new(),
            constant_cache: HashMap::new(),
            outline_costs: HashMap::new(),
            outline_site: false,
            isolated_calls: HashSet::new(),
            unroll_sites: HashSet::new(),
            observed: HashSet::new(),
            next_id: 0,
            calls: BTreeMap::new(),
            subs: HashSet::new(),
            sub_sites: HashMap::new(),
            inline_once: HashSet::new(),
            reads: HashMap::new(),
            sub_bodies: BTreeMap::new(),
            mem_keys: HashSet::new(),
            found_mem: HashSet::new(),
            impure: HashSet::new(),
            proc: None,
            vectorised: Vec::new(),
            elem_written: HashSet::new(),
        }
    }

    /// Whether evaluating `e` can change module variables.
    fn impure(&self, e: &Expr) -> bool {
        let mut found = false;
        visit(e, &mut |x| {
            if let ExprKind::Call { func, .. } = &x.kind {
                if matches!(&func.kind, ExprKind::Name(n) if self.impure.contains(n) && self.alias(n).is_none()) {
                    found = true;
                }
            }
        });
        found
    }

    /// A value as it is now, when something evaluated after it (a call) might change it:
    /// single values are copied (arrays aren't: Python sees changes to them too).
    fn freeze(&mut self, v: Val, out: &mut Vec<Stmt>) -> Val {
        match v {
            Val::Scalar(e) if !matches!(e.kind, ExprKind::Int(_) | ExprKind::Bool(_)) && self.fold(&e).is_none() => {
                let t = self.temp();
                let span = e.span;
                out.push(assign(&t, e, span));
                Val::Scalar(name(&t, span))
            }
            Val::Tuple(parts) => Val::Tuple(parts.into_iter().map(|p| self.freeze(p, out)).collect()),
            v => v,
        }
    }

    /// Evaluates `items` left to right, freezing each value that a later item could change.
    fn exprs_in_order<'e>(&mut self, items: impl IntoIterator<Item = &'e Expr>, out: &mut Vec<Stmt>) -> Result<Vec<Val>, Diag> {
        let items: Vec<&Expr> = items.into_iter().collect();
        let mut vals = Vec::new();
        for (i, e) in items.iter().enumerate() {
            let v = self.expr(e, out)?;
            let later = items[i + 1..].iter().any(|x| self.impure(x));
            vals.push(if later { self.freeze(v, out) } else { v });
        }
        Ok(vals)
    }

    /// Marks an array as needing a signal array (from the next round on).
    fn want_mem(&mut self, r: &str) {
        self.found_mem.insert(mem_key(r));
    }

    fn decide_mem(&self, r: &str, n: usize) -> bool {
        n > MAX_ARRAY || self.mem_keys.contains(&mem_key(r))
    }

    /// The elements of an array value, as scalar expressions (signal arrays: one read each).
    fn items(&mut self, v: Val, span: Span) -> Result<Vec<Expr>, Diag> {
        match v {
            Val::Array(items) => Ok(items),
            Val::Mem(banks, n) => {
                let mut items = Vec::new();
                for (b, (_, nb)) in banks.iter().zip(bank_ranges(n)) {
                    for k in 0..nb {
                        items.push(call("#aget", vec![b.clone(), int(k as i64, span), int(nb as i64, span)], span));
                    }
                }
                Ok(items)
            }
            v => Err(self.scalar(v, span).err().unwrap_or_else(|| Diag::error(span, "expected an array"))),
        }
    }

    /// The banks of an array value (register arrays are built into bundles).
    fn banks_of(&mut self, v: Val, span: Span) -> Result<(Vec<Expr>, usize), Diag> {
        match v {
            Val::Mem(banks, n) => Ok((banks, n)),
            Val::Array(items) => {
                let n = items.len();
                if n > MAX_MEM {
                    return Err(Diag::error(span, format!("arrays are limited to {MAX_MEM} elements")));
                }
                if let Some(banks) = self.vectorised_banks(&items) {
                    return Ok((banks, n));
                }
                let banks = bank_ranges(n).into_iter().map(|(off, nb)| call("#arr", items[off..off + nb].to_vec(), span)).collect();
                Ok((banks, n))
            }
            v => Err(self.scalar(v, span).err().unwrap_or_else(|| Diag::error(span, "expected an array"))),
        }
    }

    /// Python's constant index `k` (negative counts from the end), checked.
    fn index_of(&self, k: i32, n: usize, span: Span) -> Result<usize, Diag> {
        let k = k as i64;
        let k = if k < 0 { k + n as i64 } else { k };
        if !(0..n as i64).contains(&k) {
            return Err(Diag::error(span, format!("index {k} is out of range for an array of {n}")));
        }
        Ok(k as usize)
    }

    /// With `--checks`: a statement checking that runtime index `i` is in range for `n`.
    fn index_check(&mut self, i: &Expr, n: usize, out: &mut Vec<Stmt>) {
        if crate::checks_on() {
            let span = i.span;
            out.push(stmt(StmtKind::Assert(call("#ixok", vec![i.clone(), int(n as i64, span)], span)), span));
        }
    }

    /// With `--checks`: `read` (an element at runtime index `i`), checking the index first.
    fn checked_read(&mut self, i: &Expr, n: usize, read: Expr) -> Expr {
        if !crate::checks_on() {
            return read;
        }
        let span = i.span;
        call("#chk", vec![i.clone(), int(n as i64, span), read], span)
    }

    /// Element `i` of a signal array.
    fn mem_read(&mut self, banks: &[Expr], n: usize, i: Expr, ispan: Span, out: &mut Vec<Stmt>) -> Result<Expr, Diag> {
        let span = i.span;
        let ranges = bank_ranges(n);
        if let Some(k) = self.fold(&i) {
            let k = self.index_of(k, n, ispan)?;
            let b = k / bank_size();
            let (off, nb) = ranges[b];
            return Ok(call("#aget", vec![banks[b].clone(), int((k - off) as i64, span), int(nb as i64, span)], span));
        }
        let i = if ranges.len() > 1 { self.bind(i, out) } else { i };
        // Every bank reads with its own offset; out of range gives 0.
        let reads: Vec<Expr> = banks
            .iter()
            .zip(ranges)
            .map(|(b, (off, nb))| call("#aget", vec![b.clone(), minus(&i, off, span), int(nb as i64, span)], span))
            .collect();
        Ok(reads.into_iter().reduce(|a, b| bin(BinOp::Add, a, b, span)).unwrap_or_else(|| int(0, span)))
    }

    /// `arr[i] = e` (or `arr[i] += e`) on signal array `arr` of length `n`.
    fn mem_write(&mut self, arr: &str, i: Expr, e: Expr, add: bool, span: Span, out: &mut Vec<Stmt>) -> Result<(), Diag> {
        let Shape::Mem(n) = self.shape(arr) else { unreachable!("not a signal array") };
        let f = if add { "#aadd" } else { "#aset" };
        let ranges = bank_ranges(n);
        if let Some(k) = self.fold(&i) {
            let k = self.index_of(k, n, i.span)?;
            let b = k / bank_size();
            let (off, nb) = ranges[b];
            let bn = bank_name(arr, b);
            out.push(assign(&bn, call(f, vec![name(&bn, span), int((k - off) as i64, span), e, int(nb as i64, span)], span), span));
            return Ok(());
        }
        let (i, e) = if ranges.len() > 1 { (self.bind(i, out), self.bind(e, out)) } else { (i, e) };
        self.index_check(&i, n, out);
        for (b, (off, nb)) in ranges.into_iter().enumerate() {
            let bn = bank_name(arr, b);
            out.push(assign(&bn, call(f, vec![name(&bn, span), minus(&i, off, span), e.clone(), int(nb as i64, span)], span), span));
        }
        Ok(())
    }

    /// Assigns a signal array's banks to array variable `r`.
    fn assign_banks(&mut self, r: &str, banks: Vec<Expr>, span: Span, out: &mut Vec<Stmt>) {
        let names = (0..banks.len()).map(|b| bank_name(r, b)).collect();
        self.parallel_assign(names, banks, span, out);
    }

    /// `for s, v in b.items():` (or `for s in b.keys():`): visits the signals of a snapshot of
    /// `b` from the largest value (`ascending=True`: the smallest), ties in the game's signal
    /// order. Each iteration takes the top signal with a selector and removes it from the
    /// snapshot.
    #[allow(clippy::too_many_arguments)]
    fn bundle_loop(&mut self, target: &Expr, base: &Expr, items: bool, kwargs: &[(String, Expr)], body: &[Stmt], span: Span, out: &mut Vec<Stmt>) -> Result<(), Diag> {
        if self.every {
            return Err(Diag::error(span, "a loop over a bundle's signals can't be used in an `every` block")
                .with_help("it takes a few ticks per signal; write it in the main program or a process, or use a comprehension"));
        }
        let mut ascending = false;
        for (k, v) in kwargs {
            match (k.as_str(), self.fold(v)) {
                ("ascending", Some(x)) => ascending = x != 0,
                ("ascending", None) => return Err(Diag::error(v.span, "`ascending` must be a constant (True or False)")),
                _ => return Err(Diag::error(v.span, format!("`.items()` doesn't take `{k}`"))),
            }
        }
        let (s_target, v_target) = match (&target.kind, items) {
            (ExprKind::Tuple(ts), true) if ts.len() == 2 => (&ts[0], Some(&ts[1])),
            (ExprKind::Name(_), false) => (target, None),
            (_, true) => return Err(Diag::error(target.span, "loop over `.items()` with two names: `for s, v in b.items():`")),
            (_, false) => return Err(Diag::error(target.span, "loop over `.keys()` with one name: `for s in b.keys():`")),
        };
        let b = self.expr_scalar(base, out)?;
        let rest = self.temp();
        out.push(assign(&rest, b, span));
        let k = self.temp();
        let top = self.temp();
        let mut pre = vec![assign(&top, call("#rank", vec![name(&rest, span), int(0, span), Expr { kind: ExprKind::Bool(!ascending), span }], span), span)];
        self.assign_to(s_target, Val::Scalar(call("#hot", vec![name(&top, span)], span)), span, &mut pre)?;
        if let Some(v) = v_target {
            self.assign_to(v, Val::Scalar(call("#total", vec![name(&top, span)], span)), span, &mut pre)?;
        }
        pre.push(assign(&rest, bin(BinOp::Sub, name(&rest, span), name(&top, span), span), span));
        self.loops.push(Loop::Real);
        let b = self.stmts(body);
        self.loops.pop();
        pre.extend(b?);
        let range = call("range", vec![call("len", vec![name(&rest, span)], span)], span);
        out.push(stmt(StmtKind::For { target: name(&k, span), iter: range, body: pre }, span));
        Ok(())
    }

    /// `x in arr` for a signal array.
    fn mem_in(&mut self, banks: &[Expr], n: usize, x: Expr, span: Span, out: &mut Vec<Stmt>) -> Expr {
        let x = self.bind(x, out);
        let k = self.fold(&x);
        let mut tests = Vec::new();
        for (b, (_, nb)) in banks.iter().zip(bank_ranges(n)) {
            if k != Some(0) {
                let m = self.matches(b, &x, span);
                tests.push(compare(call("len", vec![m], span), CmpOp::Ne, int(0, span), span));
            }
            if k.is_none() || k == Some(0) {
                // Zeros aren't on the wire: a bank has one when it has fewer signals.
                let short = compare(call("len", vec![b.clone()], span), CmpOp::Lt, int(nb as i64, span), span);
                let zero = compare(x.clone(), CmpOp::Eq, int(0, span), span);
                tests.push(Expr { kind: ExprKind::BoolOp(BoolOp::And, vec![zero, short]), span });
            }
        }
        match tests.len() {
            0 => Expr { kind: ExprKind::Bool(false), span },
            1 => tests.pop().unwrap(),
            _ => Expr { kind: ExprKind::BoolOp(BoolOp::Or, tests), span },
        }
    }

    /// `{s: 1 for s, v in bank.items() if v == x}` (already expanded).
    fn matches(&mut self, bank: &Expr, x: &Expr, span: Span) -> Expr {
        let id = self.fresh();
        let (sn, vn) = (format!("#s{id}.s"), format!("#v{id}.v"));
        Expr {
            kind: ExprKind::DictComp {
                key: Box::new(name(&sn, span)),
                value: Box::new(int(1, span)),
                target: Box::new(Expr { kind: ExprKind::Tuple(vec![name(&sn, span), name(&vn, span)]), span }),
                iter: Box::new(method_call(bank.clone(), "items", span)),
                conds: vec![compare(name(&vn, span), CmpOp::Eq, x.clone(), span)],
            },
            span,
        }
    }

    /// `arr.index(x)` for a signal array: the first position holding `x`, or -1.
    fn mem_index(&mut self, banks: &[Expr], n: usize, x: Expr, span: Span, out: &mut Vec<Stmt>) -> Expr {
        let x = self.bind(x, out);
        let k = self.fold(&x);
        let mut firsts = Vec::new();
        for (b, (off, nb)) in banks.iter().zip(bank_ranges(n)) {
            // The matching slots (zeros too, when `x` is 0), times their positions; the
            // smallest is the first.
            let mut parts = Vec::new();
            if k != Some(0) {
                parts.push(self.matches(b, &x, span));
            }
            if k.is_none() || k == Some(0) {
                let is_zero = compare(x.clone(), CmpOp::Eq, int(0, span), span);
                parts.push(call("#azeros", vec![b.clone(), is_zero, int(nb as i64, span)], span));
            }
            let m = parts.into_iter().reduce(|a, b| bin(BinOp::Add, a, b, span)).unwrap();
            let at = bin(BinOp::Mul, m, call("#aidx", vec![int(nb as i64, span)], span), span);
            let first = call("min", vec![method_call(at, "values", span)], span);
            let first = self.bind(bin(BinOp::Sub, first, int(1, span), span), out);
            firsts.push((first, off));
        }
        // The first bank with a match (each bank's result is already -1 without one).
        let mut acc: Option<Expr> = None;
        for (f, off) in firsts.into_iter().rev() {
            let at = if off == 0 { f.clone() } else { bin(BinOp::Add, f.clone(), int(off as i64, span), span) };
            acc = Some(match acc {
                None if off == 0 => f,
                rest => {
                    let found = compare(f, CmpOp::Ge, int(0, span), span);
                    if_exp(found, at, rest.unwrap_or_else(|| int(-1, span)), span)
                }
            });
        }
        acc.unwrap_or_else(|| int(-1, span))
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

    /// Subroutines are compiled once per process: `f` in main, `P:f` in process `P`.
    fn sub_key(&self, f: &str) -> String {
        match &self.proc {
            Some(p) => format!("{p}:{f}"),
            None => f.to_string(),
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
                    Shape::Array(n) | Shape::Mem(n) => format!("an array of {n}"),
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
            Val::Mem(_, n) => Err(Diag::error(span, format!("expected a single value, but this is an array of {n}"))
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
                    Shape::Mem(k) => mem_names(&r, k, span),
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
                let mut ab = self.exprs_in_order([&**a, &**b], out)?.into_iter();
                let (va, vb) = (ab.next().unwrap(), ab.next().unwrap());
                let is_arr = |v: &Val| matches!(v, Val::Array(_) | Val::Mem(..));
                // Concatenating or repeating signal arrays goes element by element.
                let (va, vb) = if is_arr(&va) && (is_arr(&vb) || *op == BinOp::Mul) || is_arr(&vb) && *op == BinOp::Mul {
                    let va = if matches!(va, Val::Mem(..)) { Val::Array(self.items(va, a.span)?) } else { va };
                    let vb = if matches!(vb, Val::Mem(..)) { Val::Array(self.items(vb, b.span)?) } else { vb };
                    (va, vb)
                } else {
                    (va, vb)
                };
                match (op, va, vb) {
                    (BinOp::Add, Val::Array(x), Val::Array(y)) => {
                        if x.len() + y.len() > MAX_MEM {
                            return Err(Diag::error(span, format!("arrays are limited to {MAX_MEM} elements")));
                        }
                        Val::Array(x.into_iter().chain(y).collect())
                    }
                    (BinOp::Mul, Val::Array(x), Val::Scalar(k)) | (BinOp::Mul, Val::Scalar(k), Val::Array(x)) => {
                        let n = self.fold(&k).ok_or_else(|| Diag::error(k.span, "an array can only be repeated a constant number of times"))?;
                        let n = n.max(0) as usize;
                        if x.len() * n > MAX_MEM {
                            return Err(Diag::error(span, format!("arrays are limited to {MAX_MEM} elements")));
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
                        Val::Mem(banks, n) => {
                            let t = self.mem_in(&banks, n, x, span, out);
                            return Ok(Val::Scalar(if *op == CmpOp::In { t } else { Expr { kind: ExprKind::Not(Box::new(t)), span } }));
                        }
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
                let all = std::iter::once(&**first).chain(rest.iter().map(|(_, x)| x));
                let vals = self.exprs_in_order(all, out)?;
                let mut vals = vals.into_iter().zip(std::iter::once(first.span).chain(rest.iter().map(|(_, x)| x.span)));
                let (v0, s0) = vals.next().unwrap();
                let f = self.scalar(v0, s0)?;
                let mut r = Vec::new();
                for ((op, _), (v, sp)) in rest.iter().zip(vals) {
                    r.push((*op, self.scalar(v, sp)?));
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
                    (x @ (Val::Mem(..) | Val::Array(_)), y @ (Val::Mem(..) | Val::Array(_)))
                        if matches!((&x, &y), (Val::Mem(..), _) | (_, Val::Mem(..))) =>
                    {
                        let (bx, nx) = self.banks_of(x, then.span)?;
                        let (by, ny) = self.banks_of(y, orelse.span)?;
                        if nx != ny {
                            return Err(Diag::error(span, format!("the two arrays have different lengths ({nx} and {ny})")));
                        }
                        let c = self.bind(c, out);
                        Val::Mem(bx.into_iter().zip(by).map(|(p, q)| if_exp(c.clone(), p, q, span)).collect(), nx)
                    }
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
                    let bv = self.expr(base, out)?;
                    if matches!(bv, Val::Array(_) | Val::Mem(..)) {
                        return self.array_method(bv, m, args, kwargs, span, out);
                    }
                    // A bundle method: `b.total()`, `b.items()`, …
                    let b = self.scalar(bv, base.span)?;
                    // `b.nth(k)`: the signal ranked `k` from the largest, and its value.
                    if m == "nth" {
                        let [k] = args.as_slice() else {
                            return Err(Diag::error(span, "`.nth(k)` takes one argument: the rank (0 is the largest)"));
                        };
                        if let Some((kw, _)) = kwargs.first() {
                            return Err(Diag::error(span, format!("`.nth()` doesn't take a keyword argument `{kw}`")));
                        }
                        let k = self.expr_scalar(k, out)?;
                        let (b, k) = (self.bind(b, out), self.bind(k, out));
                        let top = call("#rank", vec![b, k, Expr { kind: ExprKind::Bool(true), span }], span);
                        return Ok(Val::Tuple(vec![
                            Val::Scalar(call("#hot", vec![top.clone()], span)),
                            Val::Scalar(call("#total", vec![top], span)),
                        ]));
                    }
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
                    Val::Mem(banks, n) => {
                        let i = self.expr_scalar(idx, out)?;
                        if self.fold(&i).is_some() {
                            return Ok(Val::Scalar(self.mem_read(&banks, n, i, idx.span, out)?));
                        }
                        let i = if crate::checks_on() { self.bind(i, out) } else { i };
                        let read = self.mem_read(&banks, n, i.clone(), idx.span, out)?;
                        return Ok(Val::Scalar(self.checked_read(&i, n, read)));
                    }
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
                        // A named array indexed at runtime becomes a signal array (next round).
                        if let ExprKind::Name(nm) = &base.kind {
                            if self.alias(nm).is_none() {
                                let r = self.resolve(nm);
                                self.want_mem(&r);
                            }
                        }
                        let n = items.len();
                        let i = if crate::checks_on() { self.bind(i, out) } else { i };
                        // A table of constants: one bundle constant and one read.
                        if items.len() >= 3 && items.len() <= bank_size() && items.iter().all(|x| self.fold(x).is_some()) {
                            let read = call("#aget", vec![call("#arr", items, span), i.clone(), int(n as i64, span)], span);
                            return Ok(Val::Scalar(self.checked_read(&i, n, read)));
                        }
                        // Runtime index: a select over all elements (0 if out of range).
                        let mut args = vec![i.clone()];
                        args.extend(items);
                        let read = Expr { kind: ExprKind::Call { func: Box::new(name("#select", span)), args, kwargs: vec![] }, span };
                        Val::Scalar(self.checked_read(&i, n, read))
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
            ExprKind::Tuple(items) => Val::Tuple(self.exprs_in_order(items, out)?),
            ExprKind::List(items) => {
                let mut v = Vec::new();
                for (x, i) in self.exprs_in_order(items, out)?.into_iter().zip(items) {
                    v.push(self.scalar(x, i.span)?);
                }
                if v.len() > MAX_MEM {
                    return Err(Diag::error(span, format!("arrays are limited to {MAX_MEM} elements")));
                }
                Val::Array(v)
            }
            ExprKind::ListComp { elt, target, iter, conds } => {
                let ExprKind::Name(t) = &target.kind else {
                    return Err(Diag::error(target.span, "the comprehension variable must be a single name"));
                };
                let range = is_range(iter);
                let values = if range {
                    self.iteration_values(iter, out)?
                } else {
                    match self.expr(iter, out)? {
                        // Element-wise over a signal array: bundle operations on every bank.
                        Val::Mem(banks, n) if conds.is_empty() && per_element(elt, t) && !has_call(elt, self.fns) => {
                            return self.mem_map(&banks, n, t, elt, out);
                        }
                        v => self.snapshot(v, iter.span, out)?,
                    }
                };
                let mut items = Vec::new();
                for v in values.iter().cloned() {
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
                if range && conds.is_empty() {
                    self.vectorise_range(t, elt, &values, &items);
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
        let v = self.expr(iter, out)?;
        self.snapshot(v, iter.span, out)
    }

    /// The elements of an array to iterate over. Elements might change during the loop, so
    /// iterate over a snapshot.
    fn snapshot(&mut self, v: Val, span: Span, out: &mut Vec<Stmt>) -> Result<Vec<Expr>, Diag> {
        match v {
            v @ (Val::Array(_) | Val::Mem(..)) => {
                let items = self.items(v, span)?;
                Ok(items.into_iter().map(|e| self.bind(e, out)).collect())
            }
            _ => Err(Diag::error(span, "can only iterate over `range(…)` or an array")),
        }
    }

    /// `[f(x) for x in arr]` on a signal array: a bundle comprehension per bank over the
    /// elements that aren't 0, plus `f(0)` on those that are (`#amap`, lower.rs).
    fn mem_map(&mut self, banks: &[Expr], n: usize, var: &str, elt: &Expr, out: &mut Vec<Stmt>) -> Result<Val, Diag> {
        let span = elt.span;
        let mut res = Vec::new();
        for (b, (_, nb)) in banks.iter().zip(bank_ranges(n)) {
            let id = self.fresh();
            let (sn, vn) = (format!("#s{id}.s"), format!("#v{id}.v"));
            self.aliases.push(HashMap::from([(var.to_string(), name(&vn, span))]));
            let value = self.expr_scalar(elt, out);
            self.aliases.pop();
            self.aliases.push(HashMap::from([(var.to_string(), int(0, span))]));
            let at_zero = self.expr_scalar(elt, out);
            self.aliases.pop();
            let (value, at_zero) = (value?, at_zero?);
            let comp = Expr {
                kind: ExprKind::DictComp {
                    key: Box::new(name(&sn, span)),
                    value: Box::new(value),
                    target: Box::new(Expr { kind: ExprKind::Tuple(vec![name(&sn, span), name(&vn, span)]), span }),
                    iter: Box::new(method_call(b.clone(), "items", span)),
                    conds: vec![],
                },
                span,
            };
            res.push(match self.fold(&at_zero) {
                Some(0) => comp,
                _ => call("#amap", vec![comp, b.clone(), at_zero, int(nb as i64, span)], span),
            });
        }
        Ok(Val::Mem(res, n))
    }

    /// Methods of arrays: `xs.index(v)`, `xs.as_bundle()`.
    fn array_method(&mut self, v: Val, m: &str, args: &[Expr], kwargs: &[(String, Expr)], span: Span, out: &mut Vec<Stmt>) -> Result<Val, Diag> {
        if let Some((k, _)) = kwargs.first() {
            return Err(Diag::error(span, format!("`.{m}()` doesn't take a keyword argument `{k}`")));
        }
        match (m, args) {
            ("index", [x]) => {
                let x = self.expr_scalar(x, out)?;
                let (banks, n) = self.banks_of(v, span)?;
                Ok(Val::Scalar(self.mem_index(&banks, n, x, span, out)))
            }
            ("as_bundle", []) => {
                let (banks, _) = self.banks_of(v, span)?;
                if banks.len() > 1 {
                    return Err(Diag::error(span, format!("`.as_bundle()` works on arrays of up to {} elements", bank_size())));
                }
                Ok(Val::Scalar(banks.into_iter().next().unwrap_or_else(|| call("Bundle", vec![], span))))
            }
            _ => Err(Diag::error(span, format!("arrays have no method `{m}` with {} argument(s)", args.len()))
                .with_help("array methods: `.index(v)` and `.as_bundle()`; see also `len`, `sum`, `min`, `max`, `sorted`")),
        }
    }

    fn builtin(&mut self, f: &str, args: &[Expr], kwargs: &[(String, Expr)], span: Span, out: &mut Vec<Stmt>) -> Result<Val, Diag> {
        let vals = self.exprs_in_order(args, out)?;
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
        // Drawing on a screen (`display.rs`): `#draw(screen, W, op, args…)` draws on each
        // bank, knowing which pixels it holds.
        if f == "#draw" {
            let mut vals = vals.into_iter();
            let Some(Val::Mem(banks, n)) = vals.next() else {
                return Err(Diag::error(span, "drawing needs a screen"));
            };
            let mut rest = Vec::new();
            for (v, a) in vals.zip(&args[1..]) {
                rest.push(self.scalar(v, a.span)?);
            }
            let banks = banks
                .into_iter()
                .zip(bank_ranges(n))
                .map(|(b, (off, nb))| {
                    let mut a = vec![b, int(off as i64, span), int(nb as i64, span)];
                    a.extend(rest.iter().cloned());
                    self::call("#drawb", a, span)
                })
                .collect();
            return Ok(Val::Mem(banks, n));
        }
        if let [v @ (Val::Mem(..) | Val::Array(_))] = vals.as_slice() {
            if f == "sorted" {
                let mut rev = false;
                for (k, x) in &kw {
                    match (k.as_str(), self.fold(x)) {
                        ("reverse", Some(r)) => rev = r != 0,
                        ("reverse", None) => return Err(Diag::error(x.span, "`reverse` must be constant")),
                        _ => return Err(Diag::error(x.span, format!("`sorted` doesn't take a keyword argument `{k}`"))),
                    }
                }
                let (banks, n) = self.banks_of(v.clone(), span)?;
                if n == 0 {
                    return Ok(Val::Array(vec![]));
                }
                if banks.len() > 1 {
                    return Err(Diag::error(span, format!("`sorted` works on arrays of up to {} elements", bank_size())));
                }
                let b = banks.into_iter().next().unwrap();
                return Ok(Val::Mem(vec![self::call("#asorted", vec![b, int(rev as i64, span), int(n as i64, span)], span)], n));
            }
            if f == "reversed" {
                let mut items = self.items(v.clone(), span)?;
                items.reverse();
                return Ok(Val::Array(items));
            }
        }
        if let [Val::Mem(banks, n)] = vals.as_slice() {
            let (banks, n) = (banks.clone(), *n);
            let ranges = bank_ranges(n);
            let join = |op: BoolOp, tests: Vec<Expr>| Expr { kind: ExprKind::BoolOp(op, tests), span };
            match f {
                "len" => return Ok(Val::Scalar(int(n as i64, span))),
                "sum" => {
                    let totals = banks.into_iter().map(|b| method_call(b, "total", span));
                    return Ok(Val::Scalar(totals.reduce(|a, b| bin(BinOp::Add, a, b, span)).unwrap()));
                }
                "any" | "all" => {
                    // Zeros aren't on the wire: count the signals.
                    let tests = banks
                        .into_iter()
                        .zip(ranges)
                        .map(|(b, (_, nb))| {
                            let len = self::call("len", vec![b], span);
                            if f == "any" {
                                compare(len, CmpOp::Ne, int(0, span), span)
                            } else {
                                compare(len, CmpOp::Eq, int(nb as i64, span), span)
                            }
                        })
                        .collect();
                    return Ok(Val::Scalar(join(if f == "any" { BoolOp::Or } else { BoolOp::And }, tests)));
                }
                "min" | "max" => {
                    let fname = if f == "min" { "#amin" } else { "#amax" };
                    let each: Vec<Expr> = banks.into_iter().zip(ranges).map(|(b, (_, nb))| self::call(fname, vec![b, int(nb as i64, span)], span)).collect();
                    return Ok(Val::Scalar(tree(each, &|a, b| call(f, vec![a, b]))));
                }
                _ => {}
            }
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
            ("enumerate" | "zip", _) => {
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
        let all: Vec<&Expr> = args.iter().chain(kwargs.iter().map(|(_, a)| a)).collect();
        let mut vals = self.exprs_in_order(all, out)?.into_iter();
        for (i, _) in args.iter().enumerate() {
            bound[i] = vals.next();
        }
        for (k, a) in kwargs {
            let Some(i) = def.params.iter().position(|p| &p.name == k) else {
                return Err(Diag::error(a.span, format!("`{f}` has no parameter `{k}`")));
            };
            if bound[i].is_some() {
                return Err(Diag::error(a.span, format!("`{k}` is given twice")));
            }
            bound[i] = vals.next();
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

        if let Some(value) = self.constant_call(f, &bound, span) {
            return Ok(value);
        }
        if self.subs.contains(f) && !self.every && (!self.outline_costs.contains_key(f) || self.outline_site) {
            let key = self.sub_key(f);
            *self.sub_sites.entry(key.clone()).or_default() += 1;
            if !self.inline_once.contains(&key) {
                return self.sub_call(f, &params, bound, span, out);
            }
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
            Some(RetShape::Mem(n)) => mem_names(&slot(""), n, span),
            Some(RetShape::Tuple(shapes)) => Val::Tuple(
                shapes
                    .iter()
                    .enumerate()
                    .map(|(i, s)| match s {
                        Shape::Scalar => Val::Scalar(name(&slot(&i.to_string()), span)),
                        Shape::Array(n) => Val::Array((0..*n).map(|k| name(&element(&slot(&i.to_string()), k), span)).collect()),
                        Shape::Mem(n) => mem_names(&slot(&i.to_string()), *n, span),
                    })
                    .collect(),
            ),
        })
    }

    /// A call to a subroutine: assign its (shared) parameters, `Call`, then copy the result
    /// out before anything can call it again.
    fn sub_call(&mut self, f: &str, params: &[Param], bound: Vec<Option<Val>>, span: Span, out: &mut Vec<Stmt>) -> Result<Val, Diag> {
        let key = self.sub_key(f);
        for (p, v) in params.iter().zip(bound) {
            self.assign_to(&name(&format!("{key}.{}", p.name), p.span), v.unwrap(), p.span, out)?;
        }
        if !self.sub_bodies.contains_key(&key) {
            let exit = self.fresh();
            let def = &self.fns[f];
            self.frames.push(Frame { prefix: format!("{key}."), locals: def.locals.clone(), exit, ret: None, name: f.to_string() });
            self.stack.push(f.to_string());
            let saved_loops = std::mem::take(&mut self.loops);
            let saved_aliases = std::mem::take(&mut self.aliases);
            let src = def.body.clone();
            let body = self.stmts(&src);
            self.loops = saved_loops;
            self.aliases = saved_aliases;
            self.stack.pop();
            let frame = self.frames.pop().unwrap();
            self.sub_bodies.insert(key.clone(), (exit, body?, frame.ret));
        } else if self.stack.iter().any(|s| s == f) {
            return Err(Diag::error(span, format!("`{f}` calls itself (recursion isn't supported yet)")));
        }
        *self.calls.entry(f.to_string()).or_default() += 1;
        out.push(stmt(StmtKind::Call(key.clone()), span));
        let ret = self.sub_bodies[&key].2.clone();
        let slot = |s: &str| format!("{key}.#ret{s}");
        let copy = |this: &mut Self, shape: Shape, from: &str, out: &mut Vec<Stmt>| -> Result<Val, Diag> {
            let t = this.temp();
            let v = match shape {
                Shape::Scalar => Val::Scalar(name(from, span)),
                Shape::Array(n) => Val::Array((0..n).map(|k| name(&element(from, k), span)).collect()),
                Shape::Mem(n) => mem_names(from, n, span),
            };
            this.assign_to(&name(&t, span), v, span, out)?;
            this.expr(&name(&t, span), out)
        };
        Ok(match ret {
            None => Val::None,
            Some(RetShape::Scalar) => copy(self, Shape::Scalar, &slot(""), out)?,
            Some(RetShape::Array(n)) => copy(self, Shape::Array(n), &slot(""), out)?,
            Some(RetShape::Mem(n)) => copy(self, Shape::Mem(n), &slot(""), out)?,
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
                let elem_written = self.elem_written.contains(n);
                match v {
                    Val::Scalar(e) => {
                        self.set_shape(&r, Shape::Scalar, target.span)?;
                        out.push(assign(&r, e, span));
                    }
                    Val::Array(items) => {
                        let n = items.len();
                        let mem = match self.shapes.get(&r) {
                            Some(Shape::Mem(_)) => true,
                            Some(Shape::Array(_)) => false,
                            _ => self.decide_mem(&r, n),
                        };
                        // A computed range comprehension is cheaper as a signal array (next round).
                        if !mem && self.vectorised(&items).is_some_and(|v| v.signal_array) {
                            self.want_mem(&r);
                        }
                        if mem {
                            self.set_shape(&r, Shape::Mem(n), target.span)?;
                            let (banks, _) = self.banks_of(Val::Array(items), span)?;
                            self.assign_banks(&r, banks, span, out);
                        } else {
                            if n > MAX_ARRAY {
                                return Err(Diag::error(span, format!("arrays indexed only by constants are limited to {MAX_ARRAY} elements")));
                            }
                            self.set_shape(&r, Shape::Array(n), target.span)?;
                            let names: Vec<String> = (0..n).map(|k| element(&r, k)).collect();
                            self.parallel_assign(names, items, span, out);
                        }
                    }
                    Val::Mem(banks, n) => {
                        let mem = match self.shapes.get(&r) {
                            Some(Shape::Mem(_)) => true,
                            Some(_) => false,
                            None => self.decide_mem(&r, n),
                        };
                        // An array first given a signal array's value and never written element by
                        // element is cheaper as one too (next round): a bundle register and one read
                        // per constant index, instead of a read and a register per element.
                        if !mem && self.shapes.get(&r).is_none() && !elem_written {
                            self.want_mem(&r);
                        }
                        if !mem {
                            // Only arrays indexed at runtime are signal arrays (constant
                            // indexes are cheaper on registers): copy element by element.
                            let items = self.items(Val::Mem(banks, n), span)?;
                            return self.assign_to(target, Val::Array(items), span, out);
                        }
                        self.set_shape(&r, Shape::Mem(n), target.span)?;
                        self.assign_banks(&r, banks, span, out);
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
                    v @ Val::Mem(..) => self.items(v, span)?.into_iter().map(Val::Scalar).collect(),
                    _ => return Err(Diag::error(span, "can only unpack a tuple or an array")),
                };
                if parts.len() != targets.len() {
                    return Err(Diag::error(span, format!("can't unpack {} value(s) into {} name(s)", parts.len(), targets.len())));
                }
                // Signal arrays involved (or runtime indexes): evaluate every value first, then
                // assign left to right, like Python.
                let mem_target = |this: &Self, t: &Expr| -> bool {
                    match &t.kind {
                        ExprKind::Index(base, idx) => match &base.kind {
                            ExprKind::Name(n) => {
                                let r = this.resolve(n);
                                matches!(this.shapes.get(&r), Some(Shape::Mem(_))) || this.fold(idx).is_none()
                            }
                            _ => false,
                        },
                        ExprKind::Name(n) => {
                            let r = this.resolve(n);
                            matches!(this.shapes.get(&r), Some(Shape::Mem(_))) || this.mem_keys.contains(&mem_key(&r))
                        }
                        _ => false,
                    }
                };
                if parts.iter().any(|p| matches!(p, Val::Mem(..))) || targets.iter().any(|t| mem_target(self, t)) {
                    let mut held = Vec::new();
                    for p in parts {
                        held.push(match p {
                            // Copied even when it's a name (`xs[j + 1]` with `j` a constant is
                            // element `xs.1`): an earlier target may be that variable.
                            p @ Val::Scalar(_) => self.freeze(p, out),
                            Val::Mem(banks, n) => {
                                let mut held = Vec::new();
                                for b in banks {
                                    let t = self.temp();
                                    out.push(assign(&t, b, span));
                                    held.push(name(&t, span));
                                }
                                Val::Mem(held, n)
                            }
                            p @ Val::Array(_) => {
                                let t = self.temp();
                                self.assign_to(&name(&t, span), p, span, out)?;
                                self.expr(&name(&t, span), out)?
                            }
                            _ => return Err(Diag::error(span, "can't unpack this here")),
                        });
                    }
                    for (t, p) in targets.iter().zip(held) {
                        self.assign_to(t, p, span, out)?;
                    }
                    return Ok(());
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
                            if self.fold(&i).is_none() {
                                self.want_mem(&arr);
                            }
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
                let v = if self.impure(idx) { self.freeze(v, out) } else { v };
                let b = self.expr_scalar(base, out)?;
                let k = self.expr_scalar(idx, out)?;
                let e = self.scalar(v, span)?;
                let set = Expr { kind: ExprKind::Call { func: Box::new(name("#bset", span)), args: vec![b, k, e], kwargs: vec![] }, span };
                self.assign_to(base, Val::Scalar(set), span, out)?;
            }
            ExprKind::Index(base, idx) => {
                let (arr, len) = self.array_name(base)?;
                // The value was evaluated first (as in Python); the index may change it.
                let v = if self.impure(idx) { self.freeze(v, out) } else { v };
                let i = self.expr_scalar(idx, out)?;
                let e = self.scalar(v, span)?;
                if let Some(Shape::Mem(_)) = self.shapes.get(&arr).copied() {
                    return self.mem_write(&arr, i, e, false, span, out);
                }
                if self.fold(&i).is_none() {
                    self.want_mem(&arr);
                }
                match self.fold(&i) {
                    Some(_) => {
                        let k = self.const_index(&i, len, idx.span, "")?;
                        out.push(assign(&element(&arr, k), e, span));
                    }
                    None => {
                        // Runtime index: each element takes the value if the index matches.
                        let i = self.bind(i, out);
                        let e = self.bind(e, out);
                        self.index_check(&i, len, out);
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

    /// A named array: its resolved name and length (any representation).
    fn array_name(&self, base: &Expr) -> Result<(String, usize), Diag> {
        let ExprKind::Name(n) = &base.kind else {
            return Err(Diag::error(base.span, "can only assign to elements of a named array"));
        };
        let r = self.resolve(n);
        match self.shape(&r) {
            Shape::Array(len) | Shape::Mem(len) => Ok((r, len)),
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
                let previous = self.outline_site;
                self.outline_site = self.isolated_calls.contains(&s.span.start) && self.outline_assignment(targets, value);
                let v = self.expr(value, out);
                self.outline_site = previous;
                let v = v?;
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
                if self.impure(value) {
                    // `t op= f()` where f can change t: read t first, like Python.
                    let rhs = Expr { kind: ExprKind::Binary(*op, Box::new(target.clone()), Box::new(value.clone())), span };
                    return self.stmt(&stmt(StmtKind::Assign { targets: vec![target.clone()], value: rhs }, span), out);
                }
                let v = self.expr_scalar(value, out)?;
                match &target.kind {
                    ExprKind::Name(n) => {
                        let r = self.resolve(n);
                        if let Shape::Array(_) | Shape::Mem(_) = self.shape(&r) {
                            return Err(Diag::error(target.span, format!("`{n}` is an array; `{}=` needs a single value", op.symbol())));
                        }
                        out.push(stmt(StmtKind::AugAssign { target: name(&r, target.span), op: *op, value: v }, span));
                    }
                    ExprKind::Index(base, idx) => {
                        let (arr, len) = self.array_name(base)?;
                        let i = self.expr_scalar(idx, out)?;
                        if let Shape::Mem(n) = self.shape(&arr) {
                            return match op {
                                // Adding needs no read: the one-hot index times the amount.
                                BinOp::Add => self.mem_write(&arr, i, v, true, span, out),
                                BinOp::Sub => {
                                    let neg = Expr { kind: ExprKind::Unary(UnOp::Neg, Box::new(v)), span };
                                    self.mem_write(&arr, i, neg, true, span, out)
                                }
                                _ => {
                                    let i = self.bind(i, out);
                                    let banks: Vec<Expr> = (0..bank_ranges(n).len()).map(|b| name(&bank_name(&arr, b), span)).collect();
                                    let old = self.mem_read(&banks, n, i.clone(), idx.span, out)?;
                                    let new = bin(*op, old, v, span);
                                    self.mem_write(&arr, i, new, false, span, out)
                                }
                            };
                        }
                        if self.fold(&i).is_none() {
                            self.want_mem(&arr);
                        }
                        match self.fold(&i) {
                            Some(_) => {
                                let k = self.const_index(&i, len, idx.span, "")?;
                                out.push(stmt(StmtKind::AugAssign { target: name(&element(&arr, k), target.span), op: *op, value: v }, span));
                            }
                            None => {
                                let i = self.bind(i, out);
                                let v = self.bind(v, out);
                                self.index_check(&i, len, out);
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
                        Val::Mem(_, n) => RetShape::Mem(*n),
                        Val::Tuple(parts) => RetShape::Tuple(
                            parts
                                .iter()
                                .map(|p| match p {
                                    Val::Array(xs) => Ok(Shape::Array(xs.len())),
                                    Val::Mem(_, n) => Ok(Shape::Mem(*n)),
                                    Val::Scalar(_) => Ok(Shape::Scalar),
                                    _ => Err(Diag::error(v.span, "can't return nested tuples")),
                                })
                                .collect::<Result<_, _>>()?,
                        ),
                        Val::None => return Err(Diag::error(v.span, "this function doesn't return a value")),
                    };
                    let frame = self.frames.last_mut().unwrap();
                    match &frame.ret {
                        Some(old) if !same_shape(old, &shape) => {
                            return Err(Diag::error(v.span, format!("`{fname}` returns different kinds of values on different paths")))
                        }
                        Some(_) => {}
                        None => frame.ret = Some(shape),
                    }
                    // Assign the result slots (outside the function's local scope). A signal
                    // array stays one.
                    let slot = |s: &str| format!("{prefix}#ret{s}");
                    match &val {
                        Val::Mem(..) => self.want_mem(&slot("")),
                        Val::Tuple(parts) => {
                            for (i, p) in parts.iter().enumerate() {
                                if matches!(p, Val::Mem(..)) {
                                    self.want_mem(&slot(&i.to_string()));
                                }
                            }
                        }
                        _ => {}
                    }
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
                    // The slots keep the representation of the first value they got.
                    let fix = |shapes: &HashMap<String, Shape>, s: &str, sh: Shape| match (shapes.get(s), sh) {
                        (Some(Shape::Mem(_)), Shape::Array(n)) => Shape::Mem(n),
                        (Some(Shape::Array(_)), Shape::Mem(n)) => Shape::Array(n),
                        _ => sh,
                    };
                    let frame = self.frames.last_mut().unwrap();
                    frame.ret = match frame.ret.take() {
                        Some(RetShape::Array(n)) => Some(match fix(&self.shapes, &slot(""), Shape::Array(n)) {
                            Shape::Mem(n) => RetShape::Mem(n),
                            _ => RetShape::Array(n),
                        }),
                        Some(RetShape::Mem(n)) => Some(match fix(&self.shapes, &slot(""), Shape::Mem(n)) {
                            Shape::Array(n) => RetShape::Array(n),
                            _ => RetShape::Mem(n),
                        }),
                        Some(RetShape::Tuple(parts)) => Some(RetShape::Tuple(
                            parts.into_iter().enumerate().map(|(i, sh)| fix(&self.shapes, &slot(&i.to_string()), sh)).collect(),
                        )),
                        other => other,
                    };
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
            // Without `--checks`, asserts are left out entirely (like `python -O`).
            StmtKind::Assert(e) => {
                if crate::checks_on() {
                    let c = self.expr_scalar(e, out)?;
                    out.push(stmt(StmtKind::Assert(c), span));
                }
            }
            _ => out.push(s.clone()),
        }
        Ok(())
    }

    fn for_loop(&mut self, target: &Expr, iter: &Expr, body: &[Stmt], span: Span, out: &mut Vec<Stmt>) -> Result<(), Diag> {
        // `for s, v in b.items():` / `for s in b.keys():` over a bundle.
        if let ExprKind::Call { func, args, kwargs } = &iter.kind {
            if let ExprKind::Attr(base, m) = &func.kind {
                if (m == "items" || m == "keys") && args.is_empty() && !matches!(&base.kind, ExprKind::Name(n) if self.shapes.get(&self.resolve(n)).is_some_and(|s| *s != Shape::Scalar)) {
                    return self.bundle_loop(target, base, m == "items", kwargs, body, span, out);
                }
            }
        }
        let ExprKind::Name(t) = &target.kind else {
            return Err(Diag::error(target.span, "the loop variable must be a single name"));
        };
        let is_range = matches!(&iter.kind, ExprKind::Call { func, .. } if matches!(&func.kind, ExprKind::Name(n) if n == "range"));
        let small = self.unroll_values(target, iter, body);
        if self.every || small.is_some() {
            // Unroll: one labelled block per iteration inside one for the whole loop.
            let values = match small { Some(values) => values, None => self.iteration_values(iter, out)? };
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
            // A loop variable that the body doesn't assign and that nothing reads outside the
            // body (its value after the loop is never seen) becomes a temporary: the loop's
            // counter, without a copy (see `cfg::Builder::for_range`).
            let mut written = HashSet::new();
            assigned(body, &mut written);
            let mut inside = HashMap::new();
            count_reads(body, &mut inside);
            // A function's local can only be read in that function.
            let everywhere = match self.frames.last() {
                Some(f) if f.locals.contains(t) => {
                    let mut own = HashMap::new();
                    count_reads(&self.fns[&f.name].body, &mut own);
                    own.get(t).copied()
                }
                _ => self.reads.get(t).copied(),
            };
            // (A name read nowhere, like `_`, may also be assigned in the body, by an inner
            // `for _ in …`: those writes stay as they are, dead.)
            let private = everywhere == inside.get(t).copied() && (!written.contains(t) || everywhere.is_none());
            let alias = private && everywhere.is_some();
            let r = if private { format!("#i{}.{t}", self.fresh()) } else { self.resolve(t) };
            self.set_shape(&r, Shape::Scalar, target.span)?;
            if alias {
                self.aliases.push(HashMap::from([(t.clone(), name(&r, target.span))]));
            }
            self.loops.push(Loop::Real);
            let b = self.stmts(body);
            self.loops.pop();
            if alias {
                self.aliases.pop();
            }
            let iter = Expr { kind: ExprKind::Call { func: func.clone(), args: a, kwargs: kwargs.clone() }, span: iter.span };
            out.push(stmt(StmtKind::For { target: name(&r, target.span), iter, body: b? }, span));
            return Ok(());
        }
        // `for x in xs` in sequential code: loop over indexes, reading through a select (a
        // signal array: from a snapshot of its banks).
        let items = match self.expr(iter, out)? {
            Val::Array(items) => items,
            Val::Mem(banks, n) => {
                let mut snap = Vec::new();
                for b in banks {
                    let t = self.temp();
                    out.push(assign(&t, b, span));
                    snap.push(name(&t, span));
                }
                let idx = self.temp();
                let pick = self.mem_read(&snap, n, name(&idx, span), span, out)?;
                let mut b = Vec::new();
                self.assign_to(target, Val::Scalar(pick), span, &mut b)?;
                self.loops.push(Loop::Real);
                let rest = self.stmts(body);
                self.loops.pop();
                b.extend(rest?);
                let range = call("range", vec![int(n as i64, span)], span);
                out.push(stmt(StmtKind::For { target: name(&idx, span), iter: range, body: b }, span));
                return Ok(());
            }
            _ => return Err(Diag::error(iter.span, "can only iterate over `range(…)` or an array")),
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
    // A bank of a signal array: `xs#0` → `xs`.
    if let Some((base, b)) = n.rsplit_once('#') {
        if !base.is_empty() && !b.is_empty() && b.bytes().all(|c| c.is_ascii_digit()) && !base.ends_with('.') {
            return display(base);
        }
    }
    if n.starts_with("#t") {
        return "a temporary value".into();
    }
    // A process's own variable (`P:x`) or subroutine (`P:f.x`).
    if let Some((p, rest)) = n.split_once(':') {
        if !p.is_empty() && !p.contains(['.', '#']) {
            return format!("{} in process `{p}`", quoted(rest));
        }
    }
    // A comprehension's own names: `#s4.s` → `s`; a loop's private variable: `#i4.k` → `k`.
    if n.starts_with("#s") || n.starts_with("#v") || n.starts_with("#i") {
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

/// Whether `stmts` can exit to a block outside them. (Exits to blocks inside, such as the
/// `return` of a function inlined there, end within `stmts` and don't count: treating them as
/// leaving would copy the following code into both arms of every `if` around such a call.)
fn contains_exit(stmts: &[Stmt]) -> bool {
    fn walk(stmts: &[Stmt], inner: &mut Vec<usize>) -> bool {
        stmts.iter().any(|s| match &s.kind {
            StmtKind::Exit(l) => !inner.contains(l),
            StmtKind::If { body, orelse, .. } => walk(body, inner) || walk(orelse, inner),
            StmtKind::Block { label, body } => {
                inner.push(*label);
                let out = walk(body, inner);
                inner.pop();
                out
            }
            StmtKind::While { body, .. } | StmtKind::For { body, .. } => walk(body, inner),
            _ => false,
        })
    }
    walk(stmts, &mut Vec::new())
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

/// `mem`: arrays that must be signal arrays (screens).
pub fn expand_module(m: &Module, mem: &HashSet<String>) -> Result<(Module, CallInfo), Vec<Diag>> {
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
    // Several passes: the first discovers the shape of every module-level variable (which may
    // be assigned after it is used) and which arrays are indexed at runtime; the next ones
    // expand with that knowledge, until no more arrays become signal arrays. Ports are
    // scalars.
    let mut shapes: HashMap<String, Shape> = m
        .body
        .iter()
        .filter_map(|s| match &s.kind {
            StmtKind::Port { name, .. } => Some((name.clone(), Shape::Scalar)),
            _ => None,
        })
        .collect();
    let mut mem_keys: HashSet<String> = mem.clone();
    let mut procs: HashMap<String, Span> = HashMap::new();
    for s in &m.body {
        if let StmtKind::Process { name, .. } = &s.kind {
            if name == "main" || fns.contains_key(name) || procs.insert(name.clone(), s.span).is_some() {
                errs.push(Diag::error(s.span, format!("`{name}` is already the name of a process or function")));
            }
        }
    }
    if !errs.is_empty() {
        return Err(errs);
    }
    const ROUNDS: usize = 6;
    // Subroutines called from one place, as counted by the previous round (round 0 compiles
    // every one as a subroutine; the count doesn't depend on that choice).
    let mut inline_once = HashSet::new();
    let mut reads = HashMap::new();
    count_reads(&m.body, &mut reads);
    let mut elem_written = HashSet::new();
    element_writes(&m.body, &mut elem_written);
    for round in 0..ROUNDS {
        let mut ex = Expander::new(&fns, &consts, shapes.clone());
        ex.subs = sequential_fns(&fns);
        ex.prepare_specialization(m);
        ex.inline_once = std::mem::take(&mut inline_once);
        ex.reads = reads.clone();
        ex.elem_written = elem_written.clone();
        ex.impure = impure_fns(&fns);
        ex.mem_keys = mem_keys.clone();
        let mut body = Vec::new();
        let mut errs = Vec::new();
        let mut main = Vec::new();
        for s in &m.body {
            let r: Result<(), Diag> = (|| {
                match &s.kind {
                    StmtKind::Def { .. } => {}
                    StmtKind::Port { .. } | StmtKind::Test { .. } => body.push(s.clone()),
                    StmtKind::Process { name: pname, body: b } => {
                        ex.proc = Some(pname.clone());
                        let r = ex.stmts(b);
                        ex.proc = None;
                        body.push(stmt(StmtKind::Process { name: pname.clone(), body: r? }, s.span));
                    }
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
        let new: Vec<String> = ex.found_mem.difference(&mem_keys).cloned().collect();
        inline_once = ex.sub_sites.iter().filter(|(key, n)| {
            let f = key.rsplit(':').next().unwrap();
            **n == 1 || ex.outline_costs.get(f).is_some_and(|cost| (**n - 1) * cost <= 12 + 6 * **n)
        }).map(|(k, _)| k.clone()).collect();
        if round == 0 || (!new.is_empty() && round + 1 < ROUNDS) {
            mem_keys.extend(new);
            // Carry over the shapes of names that are the same every round (inlined calls'
            // locals are renumbered when the expansion changes).
            shapes = ex
                .shapes()
                .iter()
                .filter(|(r, _)| !r.starts_with('#') && mem_key(r) == **r)
                .map(|(r, sh)| {
                    let sh = match *sh {
                        Shape::Array(n) if mem_keys.contains(r.as_str()) => Shape::Mem(n),
                        sh => sh,
                    };
                    (r.clone(), sh)
                })
                .collect();
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

/// Functions that assign module variables (declared `global`, or elements of arrays that
/// aren't their own), directly or through the functions they call.
fn impure_fns(fns: &HashMap<String, FnDef>) -> HashSet<String> {
    fn writes_global(body: &[Stmt], locals: &HashSet<String>) -> bool {
        let global_target = |t: &Expr| -> bool {
            let mut hit = false;
            let mut check = |e: &Expr| match &e.kind {
                ExprKind::Name(n) => hit |= !locals.contains(n),
                ExprKind::Index(b, _) => {
                    if let ExprKind::Name(n) = &b.kind {
                        hit |= !locals.contains(n);
                    }
                }
                _ => {}
            };
            match &t.kind {
                ExprKind::Tuple(items) | ExprKind::List(items) => items.iter().for_each(&mut check),
                _ => check(t),
            }
            hit
        };
        body.iter().any(|s| match &s.kind {
            StmtKind::Assign { targets, .. } => targets.iter().any(global_target),
            StmtKind::AugAssign { target, .. } | StmtKind::AnnAssign { target, .. } => global_target(target),
            StmtKind::For { target, body, .. } => global_target(target) || writes_global(body, locals),
            StmtKind::If { body, orelse, .. } => writes_global(body, locals) || writes_global(orelse, locals),
            StmtKind::While { body, .. } => writes_global(body, locals),
            _ => false,
        })
    }
    let mut out: HashSet<String> = fns.iter().filter(|(_, d)| writes_global(&d.body, &d.locals)).map(|(n, _)| n.clone()).collect();
    loop {
        let more: Vec<String> = fns
            .iter()
            .filter(|(n, d)| {
                !out.contains(*n) && {
                    let mut calls = false;
                    let mut f = |e: &Expr| {
                        if let ExprKind::Call { func, .. } = &e.kind {
                            if matches!(&func.kind, ExprKind::Name(c) if out.contains(c)) {
                                calls = true;
                            }
                        }
                    };
                    stmt_exprs(&d.body, &mut f);
                    calls
                }
            })
            .map(|(n, _)| n.clone())
            .collect();
        if more.is_empty() {
            return out;
        }
        out.extend(more);
    }
}

/// Calls `f` on every expression in `body` (recursively, including nested statements).
fn stmt_exprs(body: &[Stmt], f: &mut dyn FnMut(&Expr)) {
    for s in body {
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
                stmt_exprs(body, f);
                stmt_exprs(orelse, f);
            }
            StmtKind::While { cond, body } => {
                visit(cond, f);
                stmt_exprs(body, f);
            }
            StmtKind::For { iter, body, .. } => {
                visit(iter, f);
                stmt_exprs(body, f);
            }
            _ => {}
        }
    }
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
            StmtKind::Every { body, .. } | StmtKind::Process { body, .. } => count(&mut counts, body),
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
