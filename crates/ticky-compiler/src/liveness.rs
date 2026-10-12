//! Register sharing: a process's variables that are never live at the same time can use one
//! register (a scalar signal or a private bundle wire). Liveness is computed over the process's steps
//! (`cfg::Cfg`), and statement by statement inside each step, so two variables interfere when
//! one is assigned while the other still holds a value that will be read. Non-interfering
//! variables of the same class are coalesced greedily; the caller renames them.

use std::collections::{BTreeMap, BTreeSet};

use ticky_syntax::ast::{Expr, ExprKind, Stmt, StmtKind};

use crate::cfg::{Cfg, Draft, Term};

type Names = BTreeSet<String>;

/// Names read by an expression. Names in a call's function position (`b.argmax()`) are
/// `pinned` instead: renaming leaves them alone, so they must not be shared.
fn reads(e: &Expr, out: &mut Names, pinned: &mut Names) {
    match &e.kind {
        ExprKind::Name(n) => {
            out.insert(n.clone());
        }
        ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Str(_) => {}
        ExprKind::Unary(_, a) | ExprKind::Not(a) | ExprKind::Attr(a, _) => reads(a, out, pinned),
        ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
            reads(a, out, pinned);
            reads(b, out, pinned);
        }
        ExprKind::Compare(a, rest) => {
            reads(a, out, pinned);
            rest.iter().for_each(|(_, x)| reads(x, out, pinned));
        }
        ExprKind::BoolOp(_, items) | ExprKind::Tuple(items) | ExprKind::List(items) => items.iter().for_each(|x| reads(x, out, pinned)),
        ExprKind::IfExp { cond, then, orelse } => {
            for x in [cond, then, orelse] {
                reads(x, out, pinned);
            }
        }
        ExprKind::Call { func, args, kwargs } => {
            let mut f = Names::new();
            reads(func, &mut f, &mut Names::new());
            pinned.extend(f);
            args.iter().for_each(|x| reads(x, out, pinned));
            kwargs.iter().for_each(|(_, x)| reads(x, out, pinned));
        }
        ExprKind::ListComp { elt, target, iter, conds } => {
            for x in [elt, target, iter] {
                reads(x, out, pinned);
            }
            conds.iter().for_each(|x| reads(x, out, pinned));
        }
        ExprKind::Dict(items) => items.iter().for_each(|(k, v)| {
            reads(k, out, pinned);
            reads(v, out, pinned);
        }),
        ExprKind::DictComp { key, value, target, iter, conds } => {
            for x in [key, value, target, iter] {
                reads(x, out, pinned);
            }
            conds.iter().for_each(|x| reads(x, out, pinned));
        }
    }
}

/// Names an assignment target defines (anything else is pinned: it isn't a plain variable).
fn defs(e: &Expr, out: &mut Names, pinned: &mut Names) {
    match &e.kind {
        ExprKind::Name(n) => {
            out.insert(n.clone());
        }
        ExprKind::Tuple(items) => items.iter().for_each(|i| defs(i, out, pinned)),
        _ => reads(e, pinned, &mut Names::new()),
    }
}

/// A candidate variable: its class (only variables of one class share a register) and
/// whether it has an initial value (which it may be read with before it's assigned).
#[derive(Copy, Clone)]
pub struct Cand {
    pub class: u8,
    pub init: bool,
}

/// What the analysis of one step's statements collects.
#[derive(Default)]
struct Walk {
    /// Pairs of candidates that can't share a register (in order).
    edges: BTreeSet<(String, String)>,
    pinned: Names,
    /// Met a statement the analysis doesn't model.
    bail: bool,
}

impl Walk {
    /// Variables assigned together (`a, b = …`), or assigned while another is live, interfere;
    /// except that a copy `x = y` doesn't make `x` interfere with `y` (both hold one value).
    fn interfere(&mut self, defined: &Names, live: &Names, copy_of: Option<&String>) {
        for d in defined {
            for l in live.iter().chain(defined) {
                if l != d && Some(l) != copy_of {
                    let (a, b) = if d < l { (d, l) } else { (l, d) };
                    self.edges.insert((a.clone(), b.clone()));
                }
            }
        }
    }

    /// Backward liveness through straight-line statements: `live` goes from after `body` to
    /// before it. Only unconditional assignments kill; one inside an `if` arm kills on that
    /// arm only, so the old value stays live past the `if` (the lowering keeps it there).
    fn stmts(&mut self, body: &[Stmt], live: &mut Names) {
        for s in body.iter().rev() {
            match &s.kind {
                StmtKind::Assign { targets, value } => {
                    let mut d = Names::new();
                    targets.iter().for_each(|t| defs(t, &mut d, &mut self.pinned));
                    let copy_of = match &value.kind {
                        ExprKind::Name(y) => Some(y),
                        _ => None,
                    };
                    self.interfere(&d, live, copy_of);
                    live.retain(|n| !d.contains(n));
                    reads(value, live, &mut self.pinned);
                }
                StmtKind::AnnAssign { target, value, .. } => {
                    let mut d = Names::new();
                    defs(target, &mut d, &mut self.pinned);
                    if let Some(v) = value {
                        self.interfere(&d, live, None);
                        live.retain(|n| !d.contains(n));
                        reads(v, live, &mut self.pinned);
                    }
                }
                StmtKind::AugAssign { target, value, .. } => {
                    let mut d = Names::new();
                    defs(target, &mut d, &mut self.pinned);
                    self.interfere(&d, live, None);
                    live.extend(d);
                    reads(value, live, &mut self.pinned);
                }
                StmtKind::If { cond, body, orelse } => {
                    let mut other = live.clone();
                    self.stmts(body, live);
                    self.stmts(orelse, &mut other);
                    live.extend(other);
                    reads(cond, live, &mut self.pinned);
                }
                StmtKind::Expr(e) | StmtKind::Assert(e) => reads(e, live, &mut self.pinned),
                StmtKind::Pass => {}
                // Steps hold flattened straight-line code only; anything else (never expected)
                // turns sharing off.
                _ => self.bail = true,
            }
        }
    }

    /// Live candidates before step `d`, given those live after it.
    fn step(&mut self, d: &Draft, mut live: Names, cands: &BTreeMap<String, Cand>) -> Names {
        if let Some(e) = term_expr(&d.term) {
            reads(e, &mut live, &mut self.pinned);
        }
        self.stmts(&d.stmts, &mut live);
        live.retain(|n| cands.contains_key(n));
        live
    }
}

/// The expression a step's terminator reads after its statements.
fn term_expr(t: &Term) -> Option<&Expr> {
    match t {
        Term::Branch(e, ..) | Term::WaitUntil(e, _) | Term::WaitTicks(e, _) => Some(e),
        _ => None,
    }
}

/// Groups of variables of `cfg` that can share a register: each grouped candidate maps to its
/// group's representative (the member whose initial value the register must start with, if
/// any). Candidates must be the process's own variables that no one else reads.
/// Variables without a register (never read across a step boundary) are left out. A
/// candidate without an initial value that's read where it might not be assigned yet (live
/// on entry, or not in `defined`, the definitely-assigned sets on entry to each step) is left
/// alone, so a merge can't hide that error.
pub fn coalesce(cfg: &Cfg, cands: &BTreeMap<String, Cand>, defined: &[BTreeSet<String>]) -> BTreeMap<String, String> {
    let n = cfg.steps.len();
    let succs: Vec<Vec<usize>> = (0..n).map(|i| cfg.successors(i)).collect();
    let mut walk = Walk::default();
    // Each step as gen/kill sets: upward-exposed reads, and what it always assigns.
    let all: Names = cands.keys().cloned().collect();
    let mut gen = Vec::with_capacity(n);
    let mut kill = Vec::with_capacity(n);
    for d in &cfg.steps {
        gen.push(walk.step(d, Names::new(), cands));
        // (Its interference edges are meaningless: everything is live after it.)
        let through = Walk::default().step(d, all.clone(), cands);
        kill.push(all.difference(&through).cloned().collect::<Names>());
    }
    if walk.bail {
        return BTreeMap::new();
    }
    // Step-level liveness, to a fixpoint (in reverse order: most edges point forwards).
    let live_out = |live_in: &[Names], i: usize| -> Names { succs[i].iter().flat_map(|&s| live_in[s].iter().cloned()).collect() };
    let mut live_in: Vec<Names> = gen.clone();
    loop {
        let mut changed = false;
        for i in (0..n).rev() {
            let mut live = live_out(&live_in, i);
            live.retain(|v| !kill[i].contains(v));
            live.extend(gen[i].iter().cloned());
            if live != live_in[i] {
                live_in[i] = live;
                changed = true;
            }
        }
        if !changed {
            break;
        }
    }
    // Interference: assignments against what's live after them, and everything live on entry
    // (loaded together by the start pulse).
    for i in 0..n {
        walk.step(&cfg.steps[i], live_out(&live_in, i), cands);
    }
    let entry = &live_in[cfg.entry];
    walk.interfere(entry, entry, None);
    let ok = |v: &String| {
        // A variable no step reads before assigning it is only ever a wire within a step and
        // has no register to share (merging it into one would only add loads).
        let register = gen.iter().any(|g| g.contains(v));
        let unsafe_read = !cands[v].init && (entry.contains(v) || (0..n).any(|i| gen[i].contains(v) && !defined[i].contains(v)));
        register && !unsafe_read && !walk.pinned.contains(v)
    };
    let candidates: Vec<&String> = cands.keys().filter(|v| ok(v)).collect();
    let clash = |a: &String, b: &String| {
        let (a, b) = if a < b { (a, b) } else { (b, a) };
        walk.edges.contains(&(a.clone(), b.clone()))
    };
    fn colour<'a>(order: &[&'a String], cands: &BTreeMap<String, Cand>, edges: &BTreeSet<(String, String)>) -> Vec<Vec<&'a String>> {
        let clash = |a: &String, b: &String| {
            let (a, b) = if a < b { (a, b) } else { (b, a) };
            edges.contains(&(a.clone(), b.clone()))
        };
        let mut groups: Vec<Vec<&String>> = Vec::new();
        for &v in order {
            match groups.iter_mut().find(|ms| cands[ms[0]].class == cands[v].class && !ms.iter().any(|m| clash(v, m))) {
                Some(ms) => ms.push(v),
                None => groups.push(vec![v]),
            }
        }
        groups
    }
    // A hold can already serve several registers written by exactly the same steps.
    // Count distinct writer sets, rather than assuming every saved colour saves a hold.
    // Include remaining register-to-register copies as loads in the estimate. This is a
    // deliberately cheap proxy; keep the original allocation on equal estimated cost.
    let mut writers: BTreeMap<String, BTreeSet<usize>> = BTreeMap::new();
    let mut copies = Vec::new();
    fn writes(body: &[Stmt], step: usize, writers: &mut BTreeMap<String, BTreeSet<usize>>, copies: &mut Vec<(String, String)>) {
        for s in body {
            let mut d = Names::new();
            match &s.kind {
                StmtKind::Assign { targets, value } => {
                    for t in targets { defs(t, &mut d, &mut Names::new()); }
                    if let ExprKind::Name(n) = &value.kind {
                        copies.extend(d.iter().map(|x| (x.clone(), n.clone())));
                    }
                }
                StmtKind::AnnAssign { target, value: Some(_), .. } | StmtKind::AugAssign { target, .. } => defs(target, &mut d, &mut Names::new()),
                StmtKind::If { body, orelse, .. } => { writes(body, step, writers, copies); writes(orelse, step, writers, copies); }
                _ => {}
            }
            for n in d { writers.entry(n).or_default().insert(step); }
        }
    }
    for (i, d) in cfg.steps.iter().enumerate() { writes(&d.stmts, i, &mut writers, &mut copies); }
    let cost = |groups: &Vec<Vec<&String>>| {
        let holds: BTreeSet<BTreeSet<usize>> = groups.iter().filter(|ms| cands[ms[0]].class != 2).map(|ms|
            ms.iter().flat_map(|m| writers.get(*m).into_iter().flatten().copied()).collect()).collect();
        let loads = copies.iter().filter(|(a, b)| candidates.contains(&a) && candidates.contains(&b)
            && !groups.iter().any(|ms| ms.contains(&a) && ms.contains(&b))).count();
        (holds.len() + groups.iter().filter(|ms| cands[ms[0]].class == 2).count() + loads, groups.len())
    };
    let mut groups = colour(&candidates, cands, &walk.edges);
    let mut degree_order = candidates.clone();
    degree_order.sort_by_key(|v| std::cmp::Reverse(candidates.iter().filter(|w| clash(v, w)).count()));
    let mut reverse_order = candidates.clone();
    reverse_order.reverse();
    for order in [&degree_order, &reverse_order] {
        let trial = colour(order, cands, &walk.edges);
        if cost(&trial) < cost(&groups) { groups = trial; }
    }
    // Stable representatives independent of whichever traversal won.
    for ms in &mut groups { ms.sort(); }
    let mut map = BTreeMap::new();
    for ms in groups.into_iter().filter(|ms| ms.len() > 1) {
        // The member live on entry (at most one: they interfere) starts the register with its
        // initial value; otherwise any member with one, so the rest skip the
        // definite-assignment check they already passed.
        let rep = ms.iter().find(|m| entry.contains(**m)).or_else(|| ms.iter().find(|m| cands[**m].init)).unwrap_or(&ms[0]);
        for m in &ms {
            if m != rep {
                map.insert((*m).clone(), (*rep).clone());
            }
        }
    }
    map
}

/// Every name mentioned (read or assigned) anywhere in `body`.
pub fn mentioned(body: &[Stmt], out: &mut Names) {
    let mut pinned = Names::new();
    for s in body {
        match &s.kind {
            StmtKind::Assign { targets, value } => {
                targets.iter().for_each(|t| reads(t, out, &mut pinned));
                reads(value, out, &mut pinned);
            }
            StmtKind::AugAssign { target, value, .. } => {
                reads(target, out, &mut pinned);
                reads(value, out, &mut pinned);
            }
            StmtKind::AnnAssign { target, value, .. } => {
                reads(target, out, &mut pinned);
                if let Some(v) = value {
                    reads(v, out, &mut pinned);
                }
            }
            StmtKind::Expr(e) | StmtKind::Assert(e) | StmtKind::WaitUntil(e) | StmtKind::WaitTicks(e) | StmtKind::Return(Some(e)) => {
                reads(e, out, &mut pinned)
            }
            StmtKind::If { cond, body, orelse } => {
                reads(cond, out, &mut pinned);
                mentioned(body, out);
                mentioned(orelse, out);
            }
            StmtKind::While { cond, body } => {
                reads(cond, out, &mut pinned);
                mentioned(body, out);
            }
            StmtKind::For { target, iter, body } => {
                reads(target, out, &mut pinned);
                reads(iter, out, &mut pinned);
                mentioned(body, out);
            }
            StmtKind::Block { body, .. } | StmtKind::Sub { body, .. } => mentioned(body, out),
            StmtKind::Global(names) => out.extend(names.iter().cloned()),
            _ => {}
        }
    }
    out.extend(pinned);
}
