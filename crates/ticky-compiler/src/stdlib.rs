//! The standard library (SPEC §8.4): `import NAME` makes `NAME.f(...)` available.
//!
//! Before expansion, calls `lib.f(args)` become internal builtins `#lib.f(args)`, which
//! expansion passes through like any builtin and [`lower_call`] turns into IR. Peripherals
//! declared as port types (`display.Screen`, …) are handled by their own modules.

use std::collections::HashSet;

use ticky_factorio::{CmpOp as FCmp, Selector, QUALITIES};
use ticky_syntax::ast::{CmpOp, Expr, ExprKind, Module, Stmt, StmtKind};
use ticky_syntax::{Diag, Span};

use crate::bundle::{self, Kind};
use crate::ir::{Dnf, Graph, Lit, V};
use crate::lower::{self, Names};

/// Every library, with its functions (`(name, help)`); port types are listed separately.
pub const LIBRARIES: &[(&str, &[&str])] = &[
    ("display", &[]),
    ("speaker", &[]),
    ("items", &["stack_size", "rocket_capacity"]),
    ("quality", &["set", "merge", "of"]),
    ("random", &["choice", "key", "randint"]),
];

fn functions(lib: &str) -> &'static [&'static str] {
    LIBRARIES.iter().find(|(n, _)| *n == lib).map_or(&[], |(_, f)| f)
}

/// The libraries a module imports, checked; `import` statements stay in the module.
pub fn imports(m: &Module) -> Result<HashSet<String>, Vec<Diag>> {
    let mut errs = Vec::new();
    let mut out = HashSet::new();
    for s in &m.body {
        if let StmtKind::Import(n) = &s.kind {
            if LIBRARIES.iter().any(|(l, _)| l == n) {
                out.insert(n.clone());
            } else {
                let all: Vec<String> = LIBRARIES.iter().map(|(l, _)| format!("`{l}`")).collect();
                errs.push(Diag::error(s.span, format!("there is no library `{n}` (there are {})", all.join(", "))));
            }
        }
    }
    if errs.is_empty() {
        Ok(out)
    } else {
        Err(errs)
    }
}

/// Rewrites `lib.f(args)` into `#lib.f(args)` everywhere, for the imported libraries.
pub fn rewrite_calls(m: &mut Module, imported: &HashSet<String>) -> Result<(), Vec<Diag>> {
    let mut errs = Vec::new();
    for s in &mut m.body {
        stmt_exprs_mut(s, &mut |e| {
            walk_mut(e, &mut |e| {
                let ExprKind::Call { func, .. } = &mut e.kind else { return };
                let ExprKind::Attr(base, f) = &func.kind else { return };
                let ExprKind::Name(lib) = &base.kind else { return };
                if !imported.contains(lib) || lib == "display" {
                    if !imported.contains(lib) && LIBRARIES.iter().any(|(l, fs)| l == lib && fs.contains(&f.as_str())) {
                        errs.push(Diag::error(func.span, format!("`{lib}.{f}` needs `import {lib}` first")));
                    }
                    return;
                }
                if !functions(lib).contains(&f.as_str()) {
                    let fs: Vec<String> = functions(lib).iter().map(|f| format!("`{lib}.{f}`")).collect();
                    errs.push(Diag::error(func.span, format!("`{lib}` has no function `{f}`")).with_help(format!("it has {}", fs.join(", "))));
                    return;
                }
                let span = func.span;
                **func = Expr { kind: ExprKind::Name(format!("#{lib}.{f}")), span };
            })
        });
    }
    if errs.is_empty() {
        Ok(())
    } else {
        Err(errs)
    }
}

/// Whether a call is a library function returning a bundle (for type inference).
pub fn returns_bundle(f: &str) -> bool {
    matches!(f, "#items.stack_size" | "#items.rocket_capacity" | "#quality.set" | "#quality.merge" | "#random.choice")
}

/// Whether a call is a library function returning a runtime signal.
pub fn returns_signal(f: &str) -> bool {
    f == "#random.key"
}

/// Lowers `#lib.f(args)`.
pub fn lower_call(g: &mut Graph, names: &mut dyn Names, f: &str, args: &[Expr], kwargs: &[(String, Expr)], span: Span) -> Result<V, Diag> {
    let user = &f[1..];
    let arity = |n: usize| -> Result<(), Diag> {
        if args.len() == n {
            Ok(())
        } else {
            Err(Diag::error(span, format!("`{user}` takes {n} argument(s), got {}", args.len())))
        }
    };
    let every = random_every(kwargs, user)?;
    if !user.starts_with("random.") {
        if let Some((k, _)) = kwargs.first() {
            return Err(Diag::error(span, format!("`{user}` doesn't take a keyword argument `{k}`")));
        }
    }
    match user {
        "items.stack_size" | "items.rocket_capacity" => {
            arity(1)?;
            let mode = if user == "items.stack_size" { Selector::StackSize } else { Selector::RocketCapacity };
            let x = lower::expr(g, names, &args[0])?;
            match bundle::kind(g, x) {
                Kind::Bundle => Ok(g.bsel(x, mode)),
                // A signal: its value as a number (0 for fluids, virtual signals and
                // unknown items).
                Kind::Signal | Kind::SigVal => {
                    let b = g.unsig(x);
                    let r = g.bsel(b, mode);
                    Ok(g.btotal(r))
                }
                Kind::Int => Err(Diag::error(args[0].span, format!("`{user}` needs a bundle or a signal"))),
            }
        }
        "quality.set" | "quality.merge" => {
            if user == "quality.merge" {
                arity(1)?;
            } else {
                arity(2)?;
            }
            if !ticky_factorio::quality_pool() {
                return Err(Diag::error(span, format!("`{user}` needs the Quality mod")).with_help("build without `--no-quality`"));
            }
            let b = lower::expr(g, names, &args[0])?;
            let b = bundle::bundle(g, b, args[0].span)?;
            let q = match args.get(1) {
                None => return Ok(g.bsel(b, Selector::QualitySet { q: 0 })),
                Some(a) => a,
            };
            if let Some(k) = quality_const(q)? {
                return Ok(g.bsel(b, Selector::QualitySet { q: k }));
            }
            // A runtime quality number: one quality transfer per level, the one matching `q`
            // passed on (nothing if `q` is out of range).
            let qv = lower::expr(g, names, q)?;
            let qv = bundle::int(g, qv, q.span)?;
            let mut arms: Vec<(Dnf, V)> = Vec::new();
            for k in 0..QUALITIES.len() as u8 {
                let kv = g.konst(k as i32);
                let lit = Lit { op: FCmp::Eq, a: qv, b: kv };
                let x = g.bsel(b, Selector::QualitySet { q: k });
                arms.push((vec![vec![lit]], x));
            }
            Ok(g.bdec(arms))
        }
        "quality.of" => {
            arity(1)?;
            if !ticky_factorio::quality_pool() {
                return Err(Diag::error(span, "`quality.of` needs the Quality mod").with_help("build without `--no-quality`"));
            }
            let x = lower::expr(g, names, &args[0])?;
            if !bundle::kind(g, x).is_signal() {
                return Err(Diag::error(args[0].span, "`quality.of` needs a signal"));
            }
            // The signal (value 1) passes `quality ≥ k` for k = 1 … its level: the sum of
            // those filters on one wire is its level.
            let b = g.unsig(x);
            let mut acc = g.konst(0);
            for k in 1..QUALITIES.len() as u8 {
                let f = g.bsel(b, Selector::QualityFilter { cmp: FCmp::Ge, q: k });
                let t = g.btotal(f);
                acc = g.ar(ticky_factorio::ArOp::Add, acc, t);
            }
            Ok(acc)
        }
        "random.choice" | "random.key" => {
            arity(1)?;
            let b = lower::expr(g, names, &args[0])?;
            let b = bundle::bundle(g, b, args[0].span)?;
            let pick = g.bsel(b, Selector::Random { interval: every });
            Ok(if user == "random.key" { g.onehot(pick) } else { pick })
        }
        "random.randint" => {
            arity(2)?;
            let mut lim = Vec::new();
            for a in args {
                let v = lower::expr(g, names, a)?;
                let v = bundle::int(g, v, a.span)?;
                lim.push(g.as_const(v).ok_or_else(|| Diag::error(a.span, "`random.randint` needs constant bounds"))?);
            }
            let (lo, hi) = (lim[0] as i64, lim[1] as i64);
            let n = hi - lo + 1;
            let max = crate::expand::bank_size() as i64;
            if n < 1 || n > max {
                return Err(Diag::error(span, format!("`random.randint(lo, hi)` needs lo ≤ hi and at most {max} values; this has {n}")));
            }
            // A constant 1 … n on n signals (never 0, so every value is on the wire), one
            // picked at random, shifted to lo … hi.
            let table = g.bconst((0..n as usize).map(|k| (Graph::slot(k), k as i32 + 1)));
            let pick = g.bsel(table, Selector::Random { interval: every });
            let t = g.btotal(pick);
            let off = g.konst((lo - 1) as i32);
            Ok(g.ar(ticky_factorio::ArOp::Add, t, off))
        }
        _ => Err(Diag::error(span, format!("unknown function `{user}`"))),
    }
}

/// `every=N` on random functions: a new pick every N ticks.
fn random_every(kwargs: &[(String, Expr)], user: &str) -> Result<u32, Diag> {
    let mut every = 0;
    for (k, x) in kwargs {
        if k != "every" || !user.starts_with("random.") {
            return Err(Diag::error(x.span, format!("`{user}` doesn't take a keyword argument `{k}`")));
        }
        match x.kind {
            ExprKind::Int(n) if (1..=i32::MAX as i64).contains(&n) => every = n as u32,
            _ => return Err(Diag::error(x.span, "`every` must be a positive constant number of ticks")),
        }
    }
    Ok(every)
}

/// A constant quality: a name (`"rare"`) or a number 0–4. `None` for a runtime value.
pub fn quality_const(e: &Expr) -> Result<Option<u8>, Diag> {
    match &e.kind {
        ExprKind::Str(s) => QUALITIES.iter().position(|q| q == s).map(|k| Some(k as u8)).ok_or_else(|| {
            Diag::error(e.span, format!("unknown quality \"{s}\"")).with_help("use \"normal\", \"uncommon\", \"rare\", \"epic\" or \"legendary\"")
        }),
        ExprKind::Int(k) if (0..QUALITIES.len() as i64).contains(k) => Ok(Some(*k as u8)),
        ExprKind::Int(k) => Err(Diag::error(e.span, format!("quality {k} is out of range: 0 (normal) to 4 (legendary)"))),
        _ => Ok(None),
    }
}

/// A comprehension condition `s.quality OP q` (either way round), as a quality filter.
pub fn quality_cond(e: &Expr, s: &str) -> Result<Option<Selector>, Diag> {
    let ExprKind::Compare(a, rest) = &e.kind else { return Ok(None) };
    let [(op, b)] = rest.as_slice() else { return Ok(None) };
    let is_q = |x: &Expr| matches!(&x.kind, ExprKind::Attr(base, f) if f == "quality" && matches!(&base.kind, ExprKind::Name(n) if n == s));
    let (op, q) = if is_q(a) {
        (*op, b)
    } else if is_q(b) {
        (flip(*op), &**a)
    } else {
        return Ok(None);
    };
    let cmp = match op {
        CmpOp::Lt => FCmp::Lt,
        CmpOp::Gt => FCmp::Gt,
        CmpOp::Le => FCmp::Le,
        CmpOp::Ge => FCmp::Ge,
        CmpOp::Eq => FCmp::Eq,
        CmpOp::Ne => FCmp::Ne,
        _ => return Err(Diag::error(e.span, "compare `s.quality` with `<`, `>`, `<=`, `>=`, `==` or `!=`")),
    };
    if !ticky_factorio::quality_pool() {
        return Err(Diag::error(e.span, "`s.quality` needs the Quality mod").with_help("build without `--no-quality`"));
    }
    match quality_const(q)? {
        Some(q) => Ok(Some(Selector::QualityFilter { cmp, q })),
        None => Err(Diag::error(q.span, "`s.quality` can only be compared with a constant quality, e.g. `s.quality >= \"rare\"`")),
    }
}

fn flip(op: CmpOp) -> CmpOp {
    match op {
        CmpOp::Lt => CmpOp::Gt,
        CmpOp::Gt => CmpOp::Lt,
        CmpOp::Le => CmpOp::Ge,
        CmpOp::Ge => CmpOp::Le,
        o => o,
    }
}

/// Whether an expression mentions `s.quality` (outside a supported filter: an error).
pub fn mentions_quality(e: &Expr, s: &str) -> bool {
    let mut found = false;
    walk(e, &mut |x| {
        if matches!(&x.kind, ExprKind::Attr(base, f) if f == "quality" && matches!(&base.kind, ExprKind::Name(n) if n == s)) {
            found = true;
        }
    });
    found
}

/// Names whose values may depend on a random pick (directly, through other names, function
/// results or conditions), for the difftest to skip: the game's picks can't be reproduced.
pub fn random_names(m: &Module) -> HashSet<String> {
    fn tainted(e: &Expr, t: &HashSet<String>, fns: &HashSet<String>) -> bool {
        let mut hit = false;
        walk(e, &mut |x| match &x.kind {
            ExprKind::Name(n) if t.contains(n) => hit = true,
            ExprKind::Call { func, .. } => {
                if let ExprKind::Name(f) = &func.kind {
                    if f.starts_with("#random.") || fns.contains(f) {
                        hit = true;
                    }
                }
            }
            _ => {}
        });
        hit
    }
    fn target_names(e: &Expr, out: &mut Vec<String>) {
        match &e.kind {
            ExprKind::Name(n) => out.push(n.clone()),
            ExprKind::Index(b, _) | ExprKind::Attr(b, _) => target_names(b, out),
            ExprKind::Tuple(xs) | ExprKind::List(xs) => xs.iter().for_each(|x| target_names(x, out)),
            _ => {}
        }
    }
    struct St<'a> {
        t: &'a mut HashSet<String>,
        fns: &'a mut HashSet<String>,
        changed: bool,
    }
    fn stmts(body: &[Stmt], ctx: bool, func: Option<&str>, st: &mut St) {
        for s in body {
            let taint = |e: &Expr, st: &St| ctx || tainted(e, st.t, st.fns);
            let mark = |targets: &[&Expr], st: &mut St| {
                let mut names = Vec::new();
                targets.iter().for_each(|t| target_names(t, &mut names));
                for n in names {
                    st.changed |= st.t.insert(n);
                }
            };
            match &s.kind {
                StmtKind::Assign { targets, value } => {
                    if taint(value, st) || targets.iter().any(|x| tainted(x, st.t, st.fns)) {
                        mark(&targets.iter().collect::<Vec<_>>(), st);
                    }
                }
                StmtKind::AugAssign { target, value, .. } => {
                    if taint(value, st) || tainted(target, st.t, st.fns) {
                        mark(&[target], st);
                    }
                }
                StmtKind::AnnAssign { target, value: Some(value), .. } => {
                    if taint(value, st) {
                        mark(&[target], st);
                    }
                }
                StmtKind::Return(Some(e)) => {
                    if let (Some(f), true) = (func, taint(e, st)) {
                        st.changed |= st.fns.insert(f.to_string());
                    }
                }
                StmtKind::If { cond, body, orelse } => {
                    let c = taint(cond, st);
                    stmts(body, c, func, st);
                    stmts(orelse, c, func, st);
                }
                StmtKind::While { cond, body } => {
                    let c = taint(cond, st);
                    stmts(body, c, func, st);
                }
                StmtKind::For { target, iter, body } => {
                    let c = taint(iter, st);
                    if c {
                        mark(&[target], st);
                    }
                    stmts(body, c, func, st);
                }
                StmtKind::Def { name, body, .. } => stmts(body, false, Some(name), st),
                StmtKind::Every { body, .. } | StmtKind::Process { body, .. } | StmtKind::Block { body, .. } => stmts(body, ctx, func, st),
                StmtKind::Expr(e) => {
                    // `screen.fill(c)`, a call of a function that sets globals: coarse.
                    if taint(e, st) {
                        if let ExprKind::Call { func: f, .. } = &e.kind {
                            if let ExprKind::Attr(b, _) = &f.kind {
                                mark(&[b], st);
                            }
                        }
                    }
                }
                _ => {}
            }
        }
    }
    let mut t = HashSet::new();
    let mut fns = HashSet::new();
    loop {
        let mut st = St { t: &mut t, fns: &mut fns, changed: false };
        stmts(&m.body, false, None, &mut st);
        if !st.changed {
            return t;
        }
    }
}

// ---------------------------------------------------------------------------- AST walking

/// Calls `f` on every expression of `s` (and of the statements inside it), outermost first.
pub fn stmt_exprs_mut(s: &mut Stmt, f: &mut dyn FnMut(&mut Expr)) {
    let body = |b: &mut Vec<Stmt>, f: &mut dyn FnMut(&mut Expr)| {
        for s in b {
            stmt_exprs_mut(s, f);
        }
    };
    match &mut s.kind {
        StmtKind::Assign { targets, value } => {
            targets.iter_mut().for_each(&mut *f);
            f(value);
        }
        StmtKind::AugAssign { target, value, .. } => {
            f(target);
            f(value);
        }
        StmtKind::AnnAssign { target, value, .. } => {
            f(target);
            if let Some(v) = value {
                f(v);
            }
        }
        StmtKind::Expr(e) | StmtKind::Assert(e) | StmtKind::WaitUntil(e) | StmtKind::WaitTicks(e) => f(e),
        StmtKind::Return(Some(e)) => f(e),
        StmtKind::If { cond, body: b, orelse } => {
            f(cond);
            body(b, f);
            body(orelse, f);
        }
        StmtKind::While { cond, body: b } => {
            f(cond);
            body(b, f);
        }
        StmtKind::For { target, iter, body: b } => {
            f(target);
            f(iter);
            body(b, f);
        }
        StmtKind::Def { body: b, params, .. } => {
            for p in params {
                if let Some(d) = &mut p.default {
                    f(d);
                }
            }
            body(b, f)
        }
        StmtKind::Every { body: b, period } => {
            if let Some(p) = period {
                f(p);
            }
            body(b, f)
        }
        StmtKind::Process { body: b, .. } | StmtKind::Test { body: b, .. } | StmtKind::Block { body: b, .. } | StmtKind::Sub { body: b, .. } => {
            body(b, f)
        }
        StmtKind::TestSet { value, .. } => f(value),
        StmtKind::TestRun { ticks } => f(ticks),
        StmtKind::TestRunUntil { cond, max } => {
            f(cond);
            f(max);
        }
        StmtKind::Port { .. }
        | StmtKind::Return(None)
        | StmtKind::Import(_)
        | StmtKind::Pass
        | StmtKind::Break
        | StmtKind::Continue
        | StmtKind::Global(_)
        | StmtKind::Exit(_)
        | StmtKind::Call(_) => {}
    }
}

/// Calls `f` on `e` and every expression inside it, innermost first.
pub fn walk_mut(e: &mut Expr, f: &mut dyn FnMut(&mut Expr)) {
    match &mut e.kind {
        ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Str(_) | ExprKind::Name(_) => {}
        ExprKind::Unary(_, a) | ExprKind::Not(a) | ExprKind::Attr(a, _) => walk_mut(a, f),
        ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
            walk_mut(a, f);
            walk_mut(b, f);
        }
        ExprKind::Compare(a, rest) => {
            walk_mut(a, f);
            rest.iter_mut().for_each(|(_, x)| walk_mut(x, f));
        }
        ExprKind::BoolOp(_, xs) | ExprKind::Tuple(xs) | ExprKind::List(xs) => xs.iter_mut().for_each(|x| walk_mut(x, f)),
        ExprKind::IfExp { cond, then, orelse } => {
            walk_mut(cond, f);
            walk_mut(then, f);
            walk_mut(orelse, f);
        }
        ExprKind::Call { func, args, kwargs } => {
            walk_mut(func, f);
            args.iter_mut().for_each(|x| walk_mut(x, f));
            kwargs.iter_mut().for_each(|(_, x)| walk_mut(x, f));
        }
        ExprKind::ListComp { elt, target, iter, conds } => {
            walk_mut(elt, f);
            walk_mut(target, f);
            walk_mut(iter, f);
            conds.iter_mut().for_each(|x| walk_mut(x, f));
        }
        ExprKind::Dict(kvs) => kvs.iter_mut().for_each(|(k, v)| {
            walk_mut(k, f);
            walk_mut(v, f);
        }),
        ExprKind::DictComp { key, value, target, iter, conds } => {
            walk_mut(key, f);
            walk_mut(value, f);
            walk_mut(target, f);
            walk_mut(iter, f);
            conds.iter_mut().for_each(|x| walk_mut(x, f));
        }
    }
    f(e);
}

/// Read-only [`walk_mut`].
pub fn walk(e: &Expr, f: &mut dyn FnMut(&Expr)) {
    let mut c = e.clone();
    walk_mut(&mut c, &mut |x| f(x));
}
