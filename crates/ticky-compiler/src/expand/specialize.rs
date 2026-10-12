//! Conservative source optimizations. Eligibility is deliberately narrower than purity:
//! these transformations must not change repeated input sampling or observable loop writes.
use super::*;

/// Cost in scalar operations, or None for an expression outside our closed scalar subset.
fn cost(e: &Expr, names: &HashSet<String>) -> Option<usize> {
    Some(match &e.kind {
        ExprKind::Int(_) => 0,
        ExprKind::Name(n) if names.contains(n) => 0,
        ExprKind::Unary(_, a) => cost(a, names)? + 1,
        ExprKind::Binary(op, a, b) if !matches!(op, BinOp::Div) => cost(a, names)? + cost(b, names)? + 1,
        _ => return None,
    })
}

fn condition(e: &Expr, names: &HashSet<String>) -> bool {
    match &e.kind {
        ExprKind::Bool(_) => true,
        ExprKind::Compare(a, rest) => cost(a, names).is_some() && rest.iter().all(|(_, b)| cost(b, names).is_some()),
        ExprKind::BoolOp(_, xs) => xs.iter().all(|x| condition(x, names)),
        ExprKind::Not(x) => condition(x, names),
        _ => cost(e, names).is_some(),
    }
}

/// Closed integer leaf functions: no calls, nonlocal writes, live inputs, waits or asserts.
/// Even unreachable unsupported statements disqualify a function. That keeps diagnostics
/// and checks on the ordinary path instead of speculating through invalid source.
fn body_cost(body: &[Stmt], locals: &HashSet<String>, names: &HashSet<String>, loops: bool) -> Option<usize> {
    let mut total = 0;
    for s in body {
        total += match &s.kind {
            StmtKind::Assign { targets, value } if targets.iter().all(|t| matches!(&t.kind, ExprKind::Name(n) if locals.contains(n))) => cost(value, names)?,
            StmtKind::AugAssign { target, value, op } if matches!(&target.kind, ExprKind::Name(n) if locals.contains(n)) && *op != BinOp::Div => {
                cost(value, names)? + 1
            }
            StmtKind::Return(Some(e)) => cost(e, names)?,
            StmtKind::If { cond, body, orelse } if loops && condition(cond, names) => {
                body_cost(body, locals, names, loops)? + body_cost(orelse, locals, names, loops)?
            }
            StmtKind::While { cond, body } if loops && condition(cond, names) => body_cost(body, locals, names, loops)?,
            StmtKind::For { target, iter, body } if loops && matches!(&target.kind, ExprKind::Name(n) if locals.contains(n)) => {
                let ExprKind::Call { func, args, kwargs } = &iter.kind else {
                    return None;
                };
                if !matches!(&func.kind, ExprKind::Name(n) if n == "range") || !kwargs.is_empty() || args.iter().any(|a| cost(a, names).is_none()) {
                    return None;
                }
                body_cost(body, locals, names, loops)?
            }
            StmtKind::Break | StmtKind::Continue if loops => 0,
            StmtKind::Pass => 0,
            _ => return None,
        };
    }
    Some(total)
}

/// Estimate live hardware after scalar folding/CSE, not the raw source operation count.
/// Initially outline only one-argument functions; mixed constant/runtime argument tuples
/// need a call-site specialization cost model before sharing is reliably profitable.
fn straight_cost(f: &FnDef, consts: &HashMap<String, crate::ir::Cv>) -> Option<usize> {
    use crate::ir::{Graph, Iv, V};
    struct Values(HashMap<String, V>);
    impl crate::lower::Names for Values {
        fn lookup(&mut self, _: &mut Graph, n: &str, span: Span) -> Result<V, Diag> {
            self.0.get(n).copied().ok_or_else(|| Diag::error(span, "not a local scalar"))
        }
    }
    if f.params.len() != 1 {
        return None;
    }
    let mut g = Graph::new(vec![Iv::FULL]);
    let mut values = Values(consts.iter().map(|(n, v)| (n.clone(), g.cv(v))).collect());
    values.0.insert(f.params[0].name.clone(), g.src(0));
    for s in &f.body {
        match &s.kind {
            StmtKind::Assign { targets, value } => {
                let v = crate::lower::expr(&mut g, &mut values, value).ok()?;
                for t in targets {
                    let ExprKind::Name(n) = &t.kind else {
                        return None;
                    };
                    values.0.insert(n.clone(), v);
                }
            }
            StmtKind::AugAssign { target, value, op } => {
                let ExprKind::Name(n) = &target.kind else {
                    return None;
                };
                let e = bin(*op, target.clone(), value.clone(), s.span);
                let v = crate::lower::expr(&mut g, &mut values, &e).ok()?;
                values.0.insert(n.clone(), v);
            }
            StmtKind::Return(Some(e)) => {
                let v = crate::lower::expr(&mut g, &mut values, e).ok()?;
                if !g.checks.is_empty() {
                    return None;
                }
                return Some(g.reachable(&[v]).iter().map(|v| crate::lower::op_cost(&g.nodes[*v as usize])).sum());
            }
            StmtKind::Pass => {}
            _ => return None,
        }
    }
    None
}

impl Expander<'_> {
    pub(super) fn prepare_specialization(&mut self, m: &Module) {
        // Outlining also changes commit boundaries. Keep it between explicit waits,
        // or as the first statement of an iteration followed immediately by a wait.
        // Adjacent assignments could otherwise stop sampling/committing together.
        fn isolated(body: &[Stmt], starts_step: bool, out: &mut HashSet<usize>) {
            let wait = |s: &Stmt| matches!(s.kind, StmtKind::WaitTicks(_) | StmtKind::WaitUntil(_));
            for (i, s) in body.iter().enumerate() {
                if (i == 0 && starts_step || i > 0 && wait(&body[i - 1])) && body.get(i + 1).is_some_and(wait) {
                    out.insert(s.span.start);
                }
                match &s.kind {
                    StmtKind::While { body, .. } | StmtKind::Process { body, .. } => isolated(body, true, out),
                    // Every blocks and function bodies deliberately do not qualify.
                    _ => {}
                }
            }
        }
        isolated(&m.body, false, &mut self.isolated_calls);
        let ports: HashSet<&String> = m
            .body
            .iter()
            .filter_map(|s| match &s.kind {
                StmtKind::Port { name, .. } => Some(name),
                _ => None,
            })
            .collect();
        for (name, f) in self.fns {
            let mut names = f.locals.clone();
            names.extend(self.consts.keys().filter(|n| !ports.contains(n)).cloned());
            if body_cost(&f.body, &f.locals, &names, true).is_some() {
                self.constant_leaves.insert(name.clone());
            }
            if crate::opt_size() {
                if let Some(c) = body_cost(&f.body, &f.locals, &names, false).and_then(|_| straight_cost(f, self.consts)).filter(|c| *c >= 12) {
                    self.outline_costs.insert(name.clone(), c);
                    self.subs.insert(name.clone());
                }
            }
        }
        for s in &m.body {
            match &s.kind {
                StmtKind::Port { name, .. } => {
                    self.observed.insert(name.clone());
                }
                StmtKind::Every { body, .. } | StmtKind::Process { body, .. } => {
                    let mut reads = HashMap::new();
                    count_reads(body, &mut reads);
                    self.observed.extend(reads.into_keys());
                    assigned(body, &mut self.observed);
                }
                _ => {}
            }
        }
        for f in self.fns.values() {
            let mut reads = HashMap::new();
            count_reads(&f.body, &mut reads);
            self.observed.extend(reads.into_keys().filter(|n| !f.locals.contains(n)));
            globals_of(&f.body, &mut self.observed);
        }
        // Removing a loop boundary must not merge a later live input sample into the
        // entry step. Initially require a tail of local-only assignments ending in a wait.
        fn safe_tails(body: &[Stmt], observed: &HashSet<String>, out: &mut HashSet<usize>) {
            for (i, s) in body.iter().enumerate() {
                if let StmtKind::For { iter, .. } = &s.kind {
                    for next in &body[i + 1..] {
                        match &next.kind {
                            StmtKind::WaitTicks(_) | StmtKind::WaitUntil(_) => {
                                out.insert(iter.span.start);
                                break;
                            }
                            StmtKind::Assign { targets, value } if targets.iter().all(|t| matches!(t.kind, ExprKind::Name(_))) => {
                                let mut live = false;
                                visit(value, &mut |e| {
                                    live |= match &e.kind {
                                        ExprKind::Name(n) => observed.contains(n),
                                        ExprKind::Call { .. } => true,
                                        _ => false,
                                    }
                                });
                                if live {
                                    break;
                                }
                            }
                            _ => break,
                        }
                    }
                }
                if let StmtKind::While { body, .. } = &s.kind {
                    safe_tails(body, observed, out);
                }
            }
        }
        safe_tails(&m.body, &self.observed, &mut self.unroll_sites);
    }

    pub(super) fn constant_call(&mut self, f: &str, bound: &[Option<Val>], span: Span) -> Option<Val> {
        if !self.constant_leaves.contains(f) {
            return None;
        }
        let values: Option<Vec<i32>> = bound
            .iter()
            .map(|v| match v.as_ref()? {
                Val::Scalar(e) => self.fold(e),
                _ => None,
            })
            .collect();
        let values = values?;
        let key = (f.to_string(), values.clone());
        let result = if let Some(result) = self.constant_cache.get(&key) {
            *result
        } else {
            // A fresh expander has no candidates: no recursive speculative evaluation and
            // no subroutines. Leaf eligibility bounds expansion; execution is budgeted.
            let mut scratch = Expander::new(self.fns, self.consts, HashMap::new());
            let args: Vec<Expr> = values.iter().map(|v| int(*v as i64, span)).collect();
            let mut stmts = Vec::new();
            let result = (|| {
                let Val::Scalar(value) = scratch.call(f, &args, &[], span, &mut stmts).ok()? else {
                    return None;
                };
                let mut env = self.consts.clone();
                let mut assignments = HashMap::new();
                let mut budget = 10_000;
                crate::consteval::exec(&stmts, &[], &mut env, &mut assignments, &[], &mut budget).ok()?;
                eval_const(&value, &env, &[]).ok()?.int()
            })();
            self.constant_cache.insert(key, result);
            result
        };
        result.map(|v| {
            *self.calls.entry(f.to_string()).or_default() += 1;
            Val::Scalar(int(v as i64, span))
        })
    }

    /// Outlining may introduce a sampling boundary. Restrict it to a whole assignment RHS,
    /// never a subexpression such as `input + f(input)` or a call inside another argument.
    pub(super) fn outline_assignment(&self, targets: &[Expr], value: &Expr) -> bool {
        if self.every || !targets.iter().all(|t| matches!(t.kind, ExprKind::Name(_))) {
            return false;
        }
        let ExprKind::Call { func, args, kwargs } = &value.kind else {
            return false;
        };
        if !matches!(&func.kind, ExprKind::Name(n) if self.outline_costs.contains_key(n)) {
            return false;
        }
        let mut calls = false;
        for e in args.iter().chain(kwargs.iter().map(|(_, e)| e)) {
            visit(e, &mut |x| calls |= matches!(x.kind, ExprKind::Call { .. }));
        }
        !calls
    }

    pub(super) fn unroll_values(&mut self, target: &Expr, iter: &Expr, body: &[Stmt]) -> Option<Vec<Expr>> {
        if !crate::opt_size() || crate::checks_on() || self.every || !is_range(iter) || !self.unroll_sites.contains(&iter.span.start) {
            return None;
        }
        let ExprKind::Name(t) = &target.kind else {
            return None;
        };
        let ExprKind::Call { args, kwargs, .. } = &iter.kind else {
            return None;
        };
        if !kwargs.is_empty() || args.iter().any(|e| self.fold(e).is_none()) {
            return None;
        }
        let private = |n: &str| match self.frames.last() {
            Some(frame) => frame.locals.contains(n),
            None => !self.observed.contains(n),
        };
        if !private(t) {
            return None;
        }
        let mut inside = HashMap::new();
        count_reads(body, &mut inside);
        let mut own = HashMap::new();
        let reads = if let Some(frame) = self.frames.last() {
            count_reads(&self.fns[&frame.name].body, &mut own);
            &own
        } else {
            &self.reads
        };
        if reads.get(t).copied() != inside.get(t).copied() {
            return None;
        }
        let mut writes = HashSet::new();
        assigned(body, &mut writes);
        if writes.contains(t) || writes.iter().any(|n| !private(n)) {
            return None;
        }
        let mut names: HashSet<String> = inside.keys().filter(|n| private(n)).cloned().collect();
        names.extend(self.consts.keys().cloned());
        // No conditionals, nested loops, calls, exits or returns. Never duplicate a check.
        let mut operations = 0;
        for s in body {
            match &s.kind {
                StmtKind::Assign { targets, value } if targets.iter().all(|t| matches!(t.kind, ExprKind::Name(_))) => operations += cost(value, &names)?,
                StmtKind::AugAssign { target, value, .. } if matches!(target.kind, ExprKind::Name(_)) => operations += cost(value, &names)? + 1,
                _ => return None,
            }
        }
        let mut risky = false;
        for s in body {
            let e = match &s.kind {
                StmtKind::Assign { value, .. } => value,
                StmtKind::AugAssign { value, op, .. } => {
                    risky |= matches!(op, BinOp::Div | BinOp::FloorDiv | BinOp::Mod | BinOp::Pow);
                    value
                }
                _ => unreachable!(),
            };
            visit(e, &mut |x| risky |= matches!(x.kind, ExprKind::Binary(BinOp::Div | BinOp::FloorDiv | BinOp::Mod | BinOp::Pow, ..)));
        }
        if risky {
            return None;
        }
        let mut emitted = Vec::new();
        let values = self.iteration_values(iter, &mut emitted).ok()?;
        if !emitted.is_empty() || !(1..=4).contains(&values.len()) || (values.len() - 1) * operations > 5 {
            return None;
        }
        Some(values)
    }
}
