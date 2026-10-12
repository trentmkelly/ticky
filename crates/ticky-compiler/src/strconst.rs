//! String constants: `QUALITY = "legendary"` at the top level, usable wherever a quoted string
//! is (signal names, `quality=`, `type=`, port labels). Ticky has no string values, so each
//! use is replaced by its string before anything else sees the program, and the assignment
//! goes away.

use std::collections::HashMap;

use ticky_syntax::ast::{Expr, ExprKind, Module, SignalSpec, Stmt, StmtKind};
use ticky_syntax::{Diag, Span};

use crate::stdlib::{stmt_exprs_mut, walk_mut};

pub fn substitute(m: &mut Module) -> Result<(), Vec<Diag>> {
    let mut consts: HashMap<String, (String, Span)> = HashMap::new();
    let mut errs = Vec::new();
    m.body.retain(|s| {
        if let StmtKind::Assign { targets, value: Expr { kind: ExprKind::Str(text), .. } } = &s.kind {
            if let [Expr { kind: ExprKind::Name(n), .. }] = targets.as_slice() {
                if consts.contains_key(n) {
                    errs.push(Diag::error(s.span, format!("string constant `{n}` is assigned twice")));
                } else {
                    consts.insert(n.clone(), (text.clone(), s.span));
                }
                return false;
            }
        }
        true
    });
    if consts.is_empty() {
        return if errs.is_empty() { Ok(()) } else { Err(errs) };
    }
    rebound(&m.body, &consts, &mut errs);
    if !errs.is_empty() {
        return Err(errs);
    }
    let mut sub = |e: &mut Expr| {
        if let ExprKind::Name(n) = &e.kind {
            if let Some((text, _)) = consts.get(n) {
                e.kind = ExprKind::Str(text.clone());
            }
        }
    };
    for s in &mut m.body {
        if let StmtKind::Port { signal, label, .. } = &mut s.kind {
            if let Some((SignalSpec::Expr(e), _)) = signal {
                walk_mut(e, &mut sub);
            }
            if let Some(e) = label {
                walk_mut(e, &mut sub);
            }
        }
        stmt_exprs_mut(s, &mut |e| walk_mut(e, &mut sub));
    }
    Ok(())
}

/// Errors for any other binding of a string constant's name.
fn rebound(body: &[Stmt], consts: &HashMap<String, (String, Span)>, errs: &mut Vec<Diag>) {
    let named = |e: &Expr, errs: &mut Vec<Diag>| {
        let mut stack = vec![e];
        while let Some(e) = stack.pop() {
            match &e.kind {
                ExprKind::Name(n) if consts.contains_key(n) => {
                    errs.push(Diag::error(e.span, format!("`{n}` is a string constant and can't be assigned")));
                }
                ExprKind::Tuple(xs) | ExprKind::List(xs) => stack.extend(xs),
                _ => {}
            }
        }
    };
    for s in body {
        match &s.kind {
            StmtKind::Assign { targets, .. } => targets.iter().for_each(|t| named(t, errs)),
            StmtKind::AugAssign { target, .. } | StmtKind::AnnAssign { target, .. } => named(target, errs),
            StmtKind::For { target, body, .. } => {
                named(target, errs);
                rebound(body, consts, errs);
            }
            StmtKind::Def { params, body, .. } => {
                for p in params.iter().filter(|p| consts.contains_key(&p.name)) {
                    errs.push(Diag::error(p.span, format!("`{}` is a string constant and can't be a parameter", p.name)));
                }
                rebound(body, consts, errs);
            }
            StmtKind::If { body, orelse, .. } => {
                rebound(body, consts, errs);
                rebound(orelse, consts, errs);
            }
            StmtKind::While { body, .. } | StmtKind::Every { body, .. } | StmtKind::Process { body, .. } | StmtKind::Test { body, .. } => {
                rebound(body, consts, errs)
            }
            StmtKind::Port { name, .. } if consts.contains_key(name) => {
                errs.push(Diag::error(s.span, format!("`{name}` is a string constant and can't be a port")));
            }
            _ => {}
        }
    }
}
