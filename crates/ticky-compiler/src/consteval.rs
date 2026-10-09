//! Compile-time execution of top-level setup code (the *prologue*): loops, `if`s and inlined
//! calls whose values are all constant run in the compiler, so they cost no hardware.

use std::collections::HashMap;

use ticky_syntax::ast::{Expr, ExprKind, Stmt, StmtKind};
use ticky_syntax::{Diag, Span};

use crate::program::{eval_const, Port};

/// Why compile-time execution stopped.
pub enum Stop {
    /// The code needs something only known at runtime (or is too long to run).
    Runtime,
    Error(Diag),
}

enum Flow {
    Normal,
    Break,
    Continue,
    Exit(usize),
}

/// Executes `body` with constant values in `env`. `exprs` records, for each assigned name,
/// its annotation, last assigned expression (to infer bool-ness) and the assignment's span.
pub fn exec(
    body: &[Stmt],
    subs: &[crate::cfg::SubDef],
    env: &mut HashMap<String, i32>,
    exprs: &mut HashMap<String, (Option<Expr>, Expr, Span)>,
    ports: &[Port],
    budget: &mut usize,
) -> Result<(), Stop> {
    match run(body, &Ctx { subs, ports }, env, exprs, budget)? {
        Flow::Normal => Ok(()),
        _ => Err(Stop::Runtime),
    }
}

struct Ctx<'a> {
    subs: &'a [crate::cfg::SubDef],
    ports: &'a [Port],
}

fn value(e: &Expr, env: &HashMap<String, i32>, ports: &[Port]) -> Result<i32, Stop> {
    eval_const(e, env, ports).map_err(|_| Stop::Runtime)
}

#[allow(clippy::too_many_arguments)]
fn set(
    name: &str,
    v: i32,
    ann: Option<&Expr>,
    e: &Expr,
    span: Span,
    env: &mut HashMap<String, i32>,
    exprs: &mut HashMap<String, (Option<Expr>, Expr, Span)>,
    ports: &[Port],
) -> Result<(), Stop> {
    if ports.iter().any(|p| p.name == name && p.dir == ticky_syntax::ast::PortDir::Input) {
        return Err(Stop::Runtime); // reported properly by the main analysis
    }
    env.insert(name.to_string(), v);
    let ann = ann.cloned().or_else(|| exprs.get(name).and_then(|x| x.0.clone()));
    exprs.insert(name.to_string(), (ann, e.clone(), span));
    Ok(())
}

fn run(
    body: &[Stmt],
    cx: &Ctx,
    env: &mut HashMap<String, i32>,
    exprs: &mut HashMap<String, (Option<Expr>, Expr, Span)>,
    budget: &mut usize,
) -> Result<Flow, Stop> {
    let ports = cx.ports;
    for s in body {
        if *budget == 0 {
            return Err(Stop::Runtime);
        }
        *budget -= 1;
        match &s.kind {
            StmtKind::Pass => {}
            StmtKind::Expr(Expr { kind: ExprKind::Str(_), .. }) => {}
            StmtKind::Assign { targets, value: v } => {
                let (names, values): (Vec<&str>, Vec<(i32, &Expr)>) = match (&targets[..], &v.kind) {
                    ([Expr { kind: ExprKind::Name(n), .. }], _) => (vec![n.as_str()], vec![(value(v, env, ports)?, v)]),
                    ([Expr { kind: ExprKind::Tuple(ts), .. }], ExprKind::Tuple(vs)) if ts.len() == vs.len() => {
                        let mut names = Vec::new();
                        for t in ts {
                            let ExprKind::Name(n) = &t.kind else { return Err(Stop::Runtime) };
                            names.push(n.as_str());
                        }
                        let mut vals = Vec::new();
                        for x in vs {
                            vals.push((value(x, env, ports)?, x));
                        }
                        (names, vals)
                    }
                    _ => return Err(Stop::Runtime),
                };
                for (n, (k, e)) in names.into_iter().zip(values) {
                    set(n, k, None, e, s.span, env, exprs, ports)?;
                }
            }
            StmtKind::AnnAssign { target: Expr { kind: ExprKind::Name(n), .. }, ann, value: Some(v) } => {
                let k = value(v, env, ports)?;
                set(n, k, Some(ann), v, s.span, env, exprs, ports)?;
            }
            StmtKind::AugAssign { target: t @ Expr { kind: ExprKind::Name(n), .. }, op, value: v } => {
                let e = Expr { kind: ExprKind::Binary(*op, Box::new(t.clone()), Box::new(v.clone())), span: s.span };
                let k = value(&e, env, ports)?;
                set(n, k, None, &e, s.span, env, exprs, ports)?;
            }
            StmtKind::If { cond, body, orelse } => {
                let f = if value(cond, env, ports)? != 0 { body } else { orelse };
                match run(f, cx, env, exprs, budget)? {
                    Flow::Normal => {}
                    other => return Ok(other),
                }
            }
            StmtKind::While { cond, body } => {
                while value(cond, env, ports)? != 0 {
                    if *budget == 0 {
                        return Err(Stop::Runtime);
                    }
                    match run(body, cx, env, exprs, budget)? {
                        Flow::Break => break,
                        Flow::Normal | Flow::Continue => {}
                        exit => return Ok(exit),
                    }
                }
            }
            StmtKind::For { target: Expr { kind: ExprKind::Name(n), .. }, iter, body } => {
                let ExprKind::Call { func, args, .. } = &iter.kind else { return Err(Stop::Runtime) };
                if !matches!(&func.kind, ExprKind::Name(f) if f == "range") {
                    return Err(Stop::Runtime);
                }
                let mut a = Vec::new();
                for x in args {
                    a.push(value(x, env, ports)? as i64);
                }
                let (mut k, end, step) = match a.as_slice() {
                    [e] => (0, *e, 1),
                    [b, e] => (*b, *e, 1),
                    [b, e, st] if *st != 0 => (*b, *e, *st),
                    _ => return Err(Stop::Runtime),
                };
                while (step > 0 && k < end) || (step < 0 && k > end) {
                    if *budget == 0 {
                        return Err(Stop::Runtime);
                    }
                    let lit = Expr { kind: ExprKind::Int(k), span: s.span };
                    set(n, k as i32, None, &lit, s.span, env, exprs, ports)?;
                    match run(body, cx, env, exprs, budget)? {
                        Flow::Break => break,
                        Flow::Normal | Flow::Continue => {}
                        exit => return Ok(exit),
                    }
                    k += step;
                }
            }
            StmtKind::Block { label, body } => match run(body, cx, env, exprs, budget)? {
                Flow::Exit(l) if l == *label => {}
                Flow::Normal => {}
                other => return Ok(other),
            },
            StmtKind::Exit(l) => return Ok(Flow::Exit(*l)),
            StmtKind::Call(f) => {
                let (_, label, sub) = cx.subs.iter().find(|(n, ..)| n == f).ok_or(Stop::Runtime)?;
                match run(sub, cx, env, exprs, budget)? {
                    Flow::Normal => {}
                    Flow::Exit(l) if l == *label => {}
                    _ => return Err(Stop::Runtime),
                }
            }
            StmtKind::Break => return Ok(Flow::Break),
            StmtKind::Continue => return Ok(Flow::Continue),
            _ => return Err(Stop::Runtime),
        }
    }
    Ok(Flow::Normal)
}

impl From<Diag> for Stop {
    fn from(d: Diag) -> Self {
        Stop::Error(d)
    }
}
