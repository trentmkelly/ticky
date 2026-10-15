//! Sequential code → control-flow graph of *steps*. A step is straight-line code (simple `if`s
//! stay inside it and become selects) followed by one terminator. Each step becomes one state
//! of the process's state machine.
//!
//! Loops are rotated: the loop test is evaluated at the end of the step before the loop and at
//! the end of the body, so an iteration of a simple loop is a single step.

use ticky_syntax::ast::{BinOp, CmpOp, Expr, ExprKind, Stmt, StmtKind};
use ticky_syntax::{Diag, Span};

use crate::profile::{ProcProfile, RawStep};

/// Step index; `None` as a target means "halt".
pub type Target = Option<usize>;

#[derive(Clone, Debug)]
pub enum Term {
    /// Not sealed yet (only during construction).
    Open,
    Goto(Target),
    Branch(Expr, Target, Target),
    WaitUntil(Expr, Target),
    WaitTicks(Expr, Target),
    /// Call a subroutine, continuing at the target when it returns.
    Call(String, Target),
    /// Return from a subroutine to wherever it was called from.
    Return(String),
}

#[derive(Clone, Debug)]
pub struct Draft {
    pub stmts: Vec<Stmt>,
    pub term: Term,
    pub span: Span,
    /// The raw steps (see [`crate::profile`]) this step runs, in order: one, or several when
    /// steps joined by plain jumps were merged. (After a profile-guided branch merge, only
    /// the branching step's.)
    pub origin: Vec<usize>,
    /// With a profile: how often the profiled run is estimated to run this step.
    pub visits: f64,
}

pub struct Cfg {
    pub steps: Vec<Draft>,
    pub entry: usize,
    /// Entry step of each subroutine.
    pub subs: std::collections::HashMap<String, usize>,
    /// Hidden variables introduced for `for` loops.
    pub hidden: Vec<String>,
    /// The raw steps, before any merging (what a profile counts).
    pub raw: Vec<RawStep>,
}

/// What `continue` does in the innermost loop.
#[derive(Clone)]
enum Cont {
    /// `while`: re-test the condition.
    Retest(Expr, usize, usize),
    /// `for`: jump to a latch step that advances the counter.
    Latch(usize),
}

#[derive(Clone)]
struct Loop {
    brk: usize,
    cont: Cont,
}

struct Builder<'a> {
    steps: Vec<Draft>,
    cur: usize,
    loops: Vec<Loop>,
    /// Step that follows each labelled block (for `Exit`).
    labels: std::collections::HashMap<usize, usize>,
    /// Labels whose exit returns from a subroutine.
    returns: std::collections::HashMap<usize, String>,
    hidden: Vec<String>,
    /// Evaluates a constant expression, if it is one.
    konst: &'a dyn Fn(&Expr) -> Option<i32>,
}

/// Statements that can stay inside a step (after flattening any inlined blocks).
fn is_simple(stmts: &[Stmt]) -> bool {
    stmts.iter().all(|s| match &s.kind {
        StmtKind::Assign { .. } | StmtKind::AugAssign { .. } | StmtKind::AnnAssign { .. } | StmtKind::Pass | StmtKind::Assert(_) => true,
        StmtKind::Expr(_) => true,
        StmtKind::If { .. } | StmtKind::Block { .. } => crate::expand::flattenable(s),
        _ => false,
    })
}

fn name(n: &str, span: Span) -> Expr {
    Expr { kind: ExprKind::Name(n.to_string()), span }
}

fn int(v: i32, span: Span) -> Expr {
    Expr { kind: ExprKind::Int(v as i64), span }
}

fn assign(target: &str, value: Expr, span: Span) -> Stmt {
    Stmt { kind: StmtKind::Assign { targets: vec![name(target, span)], value }, span }
}

/// Whether `stmts` read and write the name `var` (anywhere, including nested blocks).
fn uses(stmts: &[Stmt], var: &str) -> (bool, bool) {
    let (mut read, mut written) = (false, false);
    let expr = |e: &Expr, read: &mut bool| {
        crate::expand::visit(e, &mut |x| *read |= matches!(&x.kind, ExprKind::Name(n) if n == var));
    };
    for s in stmts {
        let is_var = |t: &Expr| matches!(&t.kind, ExprKind::Name(n) if n == var);
        match &s.kind {
            StmtKind::Assign { targets, value } => {
                for t in targets {
                    let mut hit = false;
                    expr(t, &mut hit);
                    if is_var(t) || matches!(&t.kind, ExprKind::Tuple(_) | ExprKind::List(_)) && hit {
                        written = true;
                    } else {
                        read |= hit;
                    }
                }
                expr(value, &mut read);
            }
            StmtKind::AugAssign { target, value, .. } | StmtKind::AnnAssign { target, value: Some(value), .. } => {
                if is_var(target) {
                    written = true;
                }
                expr(target, &mut read);
                expr(value, &mut read);
            }
            StmtKind::AnnAssign { target, value: None, .. } => written |= is_var(target),
            StmtKind::Expr(e) | StmtKind::Assert(e) | StmtKind::WaitUntil(e) | StmtKind::WaitTicks(e) | StmtKind::Return(Some(e)) => {
                expr(e, &mut read)
            }
            StmtKind::If { cond, body, orelse } => {
                expr(cond, &mut read);
                for b in [body, orelse] {
                    let (r, w) = uses(b, var);
                    read |= r;
                    written |= w;
                }
            }
            StmtKind::While { cond: e, body } | StmtKind::For { iter: e, body, .. } => {
                expr(e, &mut read);
                if let StmtKind::For { target, .. } = &s.kind {
                    written |= is_var(target);
                }
                let (r, w) = uses(body, var);
                read |= r;
                written |= w;
            }
            StmtKind::Block { body, .. } => {
                let (r, w) = uses(body, var);
                read |= r;
                written |= w;
            }
            // Anything else might do anything.
            StmtKind::Global(_) | StmtKind::Def { .. } | StmtKind::Sub { .. } => (read, written) = (true, true),
            _ => {}
        }
    }
    (read, written)
}

impl Builder<'_> {
    fn new_step(&mut self, span: Span) -> usize {
        self.steps.push(Draft { stmts: Vec::new(), term: Term::Open, span, origin: Vec::new(), visits: 0.0 });
        self.steps.len() - 1
    }

    fn open(&self) -> bool {
        matches!(self.steps[self.cur].term, Term::Open)
    }

    fn seal(&mut self, t: Term) {
        if self.open() {
            self.steps[self.cur].term = t;
        }
    }

    fn block(&mut self, stmts: &[Stmt]) -> Result<(), Diag> {
        for s in stmts {
            self.stmt(s)?;
        }
        Ok(())
    }

    /// Starts a fresh step after the current one (which falls through to it).
    fn fallthrough(&mut self, span: Span) -> usize {
        let n = self.new_step(span);
        self.seal(Term::Goto(Some(n)));
        self.cur = n;
        n
    }

    /// Puts a simple `if` or block into the current step, its exits flattened away; false if
    /// it isn't simple, or flattening would copy too much code, so it should become steps
    /// instead. (Each early exit copies the code after it into both arms: a function calling
    /// k inlined functions with early `return`s flattens to 2^k copies of its tail. The
    /// examples need a budget of 6 at most.)
    fn flat_in_step(&mut self, s: &Stmt) -> bool {
        if !is_simple(std::slice::from_ref(s)) {
            return false;
        }
        let mut budget = 1_000;
        let Ok(flat) = crate::expand::flatten(vec![s.clone()], &mut budget) else { return false };
        self.steps[self.cur].stmts.extend(flat);
        true
    }

    fn stmt(&mut self, s: &Stmt) -> Result<(), Diag> {
        match &s.kind {
            StmtKind::Assign { .. }
            | StmtKind::AugAssign { .. }
            | StmtKind::AnnAssign { .. }
            | StmtKind::Pass
            | StmtKind::Expr(_)
            | StmtKind::Assert(_) => {
                self.steps[self.cur].stmts.push(s.clone());
            }
            StmtKind::Block { label, body } => {
                if self.flat_in_step(s) {
                    return Ok(());
                }
                let after = self.new_step(s.span);
                self.labels.insert(*label, after);
                self.block(body)?;
                self.seal(Term::Goto(Some(after)));
                self.cur = after;
            }
            StmtKind::Exit(label) => {
                match self.returns.get(label) {
                    Some(f) => {
                        let f = f.clone();
                        self.seal(Term::Return(f));
                    }
                    None => {
                        let target = *self.labels.get(label).expect("exit inside its block");
                        self.seal(Term::Goto(Some(target)));
                    }
                }
                self.cur = self.new_step(s.span); // unreachable code after the exit
            }
            StmtKind::Call(f) => {
                let cont = self.new_step(s.span);
                self.seal(Term::Call(f.clone(), Some(cont)));
                self.cur = cont;
            }
            StmtKind::Sub { .. } => return Err(Diag::error(s.span, "internal error: nested subroutine")),
            StmtKind::If { cond, body, orelse } => {
                if self.flat_in_step(s) {
                    return Ok(());
                }
                let t = self.new_step(s.span);
                let j = self.new_step(s.span);
                let f = if orelse.is_empty() { j } else { self.new_step(s.span) };
                self.seal(Term::Branch(cond.clone(), Some(t), Some(f)));
                self.cur = t;
                self.block(body)?;
                self.seal(Term::Goto(Some(j)));
                if f != j {
                    self.cur = f;
                    self.block(orelse)?;
                    self.seal(Term::Goto(Some(j)));
                }
                self.cur = j;
            }
            StmtKind::While { cond, body } => {
                let b = self.new_step(s.span);
                let x = self.new_step(s.span);
                self.seal(Term::Branch(cond.clone(), Some(b), Some(x)));
                self.loops.push(Loop { brk: x, cont: Cont::Retest(cond.clone(), b, x) });
                self.cur = b;
                self.block(body)?;
                self.seal(Term::Branch(cond.clone(), Some(b), Some(x)));
                self.loops.pop();
                self.cur = x;
            }
            StmtKind::For { target, iter, body } => self.for_range(s, target, iter, body)?,
            StmtKind::Break => {
                let l = self.loops.last().cloned().ok_or_else(|| Diag::error(s.span, "`break` outside a loop"))?;
                self.seal(Term::Goto(Some(l.brk)));
                self.cur = self.new_step(s.span); // unreachable code after `break`
            }
            StmtKind::Continue => {
                let l = self.loops.last().cloned().ok_or_else(|| Diag::error(s.span, "`continue` outside a loop"))?;
                match l.cont {
                    Cont::Retest(c, b, x) => self.seal(Term::Branch(c, Some(b), Some(x))),
                    Cont::Latch(latch) => self.seal(Term::Goto(Some(latch))),
                }
                self.cur = self.new_step(s.span);
            }
            StmtKind::WaitUntil(c) => {
                if !self.steps[self.cur].stmts.is_empty() {
                    self.fallthrough(s.span);
                }
                let next = self.new_step(s.span);
                self.seal(Term::WaitUntil(c.clone(), Some(next)));
                self.cur = next;
            }
            StmtKind::WaitTicks(n) => {
                if !self.steps[self.cur].stmts.is_empty() {
                    self.fallthrough(s.span);
                }
                let next = self.new_step(s.span);
                self.seal(Term::WaitTicks(n.clone(), Some(next)));
                self.cur = next;
            }
            StmtKind::Return(_) => return Err(Diag::error(s.span, "`return` outside a function")),
            StmtKind::Global(_) => return Err(Diag::error(s.span, "`global` is only meaningful inside a function")),
            StmtKind::Def { .. } => return Err(Diag::error(s.span, "`def` isn't supported yet (planned for level 2)")),
            StmtKind::Process { .. } => return Err(Diag::error(s.span, "processes must be declared at the top level of the file")),
            StmtKind::Every { .. } | StmtKind::Port { .. } | StmtKind::Test { .. } | StmtKind::Import(_) => {
                return Err(Diag::error(s.span, "declarations must be at the top level of the file"))
            }
            StmtKind::TestSet { .. } | StmtKind::TestRun { .. } | StmtKind::TestRunUntil { .. } => {
                return Err(Diag::error(s.span, "`set` and `run` can only be used in tests"))
            }
        }
        Ok(())
    }

    fn for_range(&mut self, s: &Stmt, target: &Expr, iter: &Expr, body: &[Stmt]) -> Result<(), Diag> {
        let ExprKind::Name(var) = &target.kind else {
            return Err(Diag::error(target.span, "the loop variable must be a single name"));
        };
        let args = match &iter.kind {
            ExprKind::Call { func, args, kwargs }
                if matches!(&func.kind, ExprKind::Name(n) if n == "range") && kwargs.is_empty() && (1..=3).contains(&args.len()) =>
            {
                args
            }
            _ => {
                return Err(Diag::error(iter.span, "only `for … in range(…)` loops are supported so far")
                    .with_help("arrays and bundles arrive in later levels"))
            }
        };
        let sp = s.span;
        let (start, end) = match args.len() {
            1 => (int(0, sp), args[0].clone()),
            _ => (args[0].clone(), args[1].clone()),
        };
        let step = match args.get(2) {
            None => 1,
            Some(e) => match (self.konst)(e) {
                Some(0) => return Err(Diag::error(e.span, "the range step can't be 0")),
                Some(k) => k,
                None => return Err(Diag::error(e.span, "the range step must be a constant")),
            },
        };
        // A temporary loop variable (`#…`, or `P:#…` in a process: the expander made it
        // private to the loop, so its value after the loop is never read) that the body only
        // reads is the counter itself; one the body doesn't use at all counts down to 0, so
        // `range(n)` needs no register for `n`.
        let (read, written) = uses(body, var);
        let private = var.split_once(':').map_or(var.as_str(), |(_, own)| own).starts_with('#') && !written;
        let countdown = private && !read && step == 1 && (self.konst)(&start) == Some(0) && (self.konst)(&end).is_none();
        let id = self.hidden.len();
        let k = if private { var.clone() } else { format!("{var}#k{id}") };
        self.hidden.push(k.clone());
        let (start, end, step) = if countdown { (end, int(0, sp), -1) } else { (start, end, step) };
        // The end is evaluated once, before the loop (Python semantics).
        let end = if (self.konst)(&end).is_some() {
            end
        } else {
            let e = format!("{var}#end{id}");
            self.hidden.push(e.clone());
            self.steps[self.cur].stmts.push(assign(&e, end, sp));
            name(&e, sp)
        };
        self.steps[self.cur].stmts.push(assign(&k, start, sp));
        let test = Expr {
            kind: ExprKind::Compare(Box::new(name(&k, sp)), vec![(if step > 0 { CmpOp::Lt } else { CmpOp::Gt }, end)]),
            span: sp,
        };
        let advance = Stmt {
            kind: StmtKind::AugAssign { target: name(&k, sp), op: BinOp::Add, value: int(step, sp) },
            span: sp,
        };
        let b = self.new_step(sp);
        let x = self.new_step(sp);
        let latch = self.new_step(sp);
        self.steps[latch].stmts.push(advance.clone());
        self.steps[latch].term = Term::Branch(test.clone(), Some(b), Some(x));
        self.seal(Term::Branch(test.clone(), Some(b), Some(x)));
        self.loops.push(Loop { brk: x, cont: Cont::Latch(latch) });
        self.cur = b;
        // Python leaves the loop variable at its last value, so it is a copy of the counter.
        if !private {
            self.steps[b].stmts.push(assign(var, name(&k, sp), sp));
        }
        self.block(body)?;
        if self.open() {
            self.steps[self.cur].stmts.push(advance);
            self.seal(Term::Branch(test, Some(b), Some(x)));
        }
        self.loops.pop();
        self.cur = x;
        Ok(())
    }
}

/// Static targets. A call's continuation counts (it's reached when the subroutine returns);
/// a return's targets are its callers' continuations, see [`Cfg::successors`].
fn targets(t: &Term) -> Vec<Target> {
    match t {
        Term::Open | Term::Return(_) => vec![],
        Term::Goto(a) | Term::WaitUntil(_, a) | Term::WaitTicks(_, a) | Term::Call(_, a) => vec![*a],
        Term::Branch(_, a, b) => vec![*a, *b],
    }
}

fn retarget(t: &mut Term, f: impl Fn(Target) -> Target) {
    match t {
        Term::Open | Term::Return(_) => {}
        Term::Goto(a) | Term::WaitUntil(_, a) | Term::WaitTicks(_, a) | Term::Call(_, a) => *a = f(*a),
        Term::Branch(_, a, b) => {
            *a = f(*a);
            *b = f(*b);
        }
    }
}

/// Largest step (in statements) copied into a predecessor that jumps to it.
const MAX_COPY: usize = 6;

/// Merges steps joined by a plain jump: each step costs at least two ticks and a few
/// combinators, so `A; goto B` becomes one step running A's code and then B's. When B has
/// other predecessors too, it is copied, if small. B must not wait: what A writes has to
/// be visible during the wait. Entry steps (`protected`) keep their identity.
fn fuse(steps: &mut [Draft], protected: &[usize], mut est: Option<&mut Est>) {
    let preds = |steps: &[Draft], b: usize| -> usize {
        steps.iter().map(|d| targets(&d.term).into_iter().filter(|t| *t == Some(b)).count()).sum::<usize>()
            + if protected.contains(&b) { 1 } else { 0 }
    };
    let mut budget = 4 * steps.len();
    loop {
        let mut changed = false;
        for a in 0..steps.len() {
            let Term::Goto(Some(b)) = steps[a].term else { continue };
            if b == a || matches!(steps[b].term, Term::WaitUntil(..) | Term::WaitTicks(..) | Term::Open) {
                continue;
            }
            let only = preds(steps, b) == 1;
            // With `--opt=size`, only copy when that removes `b` (every way into it is a plain
            // jump, so each gets a copy and `b` goes): a copy for some predecessors saves
            // those paths a step (2 ticks) but adds code.
            let partial = || steps.iter().filter(|d| matches!(d.term, Term::Goto(Some(t)) if t == b)).count() != preds(steps, b);
            // With a profile: never copy into a predecessor that didn't take this jump; copy
            // bigger steps into one that took it often.
            let cap = match est.as_deref().filter(|_| crate::profile::guide().copy) {
                Some(e) if e.get(a, Some(b)) == 0.0 => 0,
                Some(e) if e.get(a, Some(b)) >= hot_min() => HOT_COPY,
                _ => MAX_COPY,
            };
            if !only && (!crate::copy_tails() || steps[b].stmts.len() > cap || cap == 0 || budget == 0 || crate::opt_size() && partial()) {
                continue;
            }
            if !only {
                budget -= 1;
            }
            let (stmts, term, origin) = (steps[b].stmts.clone(), steps[b].term.clone(), steps[b].origin.clone());
            steps[a].stmts.extend(stmts);
            steps[a].term = term;
            steps[a].origin.extend(origin);
            if let Some(e) = est.as_deref_mut() {
                e.inline(a, &[Some(b)], only);
            }
            if only {
                // `b` is now unreachable (dropped below).
                steps[b].stmts.clear();
                steps[b].term = Term::Goto(None);
            }
            changed = true;
        }
        if !changed {
            return;
        }
    }
}

/// A jump taken at least this often (in the profile) is hot: 8, or `TICKY_PGO_HOT` (the PGO
/// fuzzer uses 1, as its random programs' loops are short).
fn hot_min() -> f64 {
    static HOT: std::sync::OnceLock<f64> = std::sync::OnceLock::new();
    *HOT.get_or_init(|| std::env::var("TICKY_PGO_HOT").ok().and_then(|v| v.parse().ok()).unwrap_or(8.0))
}
/// Largest step copied into a hot predecessor, or merged into a branch whose hot side it is.
const HOT_COPY: usize = 32;

/// Estimated transition counts between steps while they are being merged: the profile's
/// counts at first (steps are still raw steps then), updated as steps absorb others.
struct Est {
    e: std::collections::HashMap<(usize, Target), f64>,
}

impl Est {
    fn new(p: &ProcProfile) -> Est {
        Est { e: p.edges.iter().map(|(&k, &n)| (k, n as f64)).collect() }
    }

    fn get(&self, a: usize, t: Target) -> f64 {
        self.e.get(&(a, t)).copied().unwrap_or(0.0)
    }

    fn outs(&self, a: usize) -> Vec<(Target, f64)> {
        let mut v: Vec<(Target, f64)> = self.e.iter().filter(|((x, _), _)| *x == a).map(|((_, t), n)| (*t, *n)).collect();
        v.sort_by_key(|(t, _)| *t);
        v
    }

    /// Step `a` now runs the code of `arms` (some of its targets) after its own and continues
    /// where they continue. `gone`: the arms are no longer reached any other way.
    fn inline(&mut self, a: usize, arms: &[Target], gone: bool) {
        let mut add: Vec<(Target, f64)> = Vec::new();
        for &arm in arms {
            let n = self.e.remove(&(a, arm)).unwrap_or(0.0);
            let Some(x) = arm else { continue };
            let outs = self.outs(x);
            let total: f64 = outs.iter().map(|(_, k)| k).sum();
            if total > 0.0 {
                let share = (n / total).min(1.0);
                for (t, k) in outs {
                    add.push((t, k * share));
                    // What is left of `x`'s own traffic.
                    self.e.insert((x, t), if gone { 0.0 } else { k * (1.0 - share) });
                }
            }
        }
        for (t, k) in add {
            *self.e.entry((a, t)).or_insert(0.0) += k;
        }
    }
}

/// Whether `stmts` assign a branch temporary (`#pgo…`), which then can't be put inside
/// another `if` (it is read after it).
fn has_temp(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match &s.kind {
        StmtKind::Assign { targets, .. } => targets.iter().any(|t| matches!(&t.kind, ExprKind::Name(n) if n.starts_with("#pgo"))),
        StmtKind::If { body, orelse, .. } => has_temp(body) || has_temp(orelse),
        _ => false,
    })
}

/// Names `stmts` assign anywhere (an element assignment `xs[i] = v` assigns `xs`).
fn assigned(stmts: &[Stmt], out: &mut std::collections::BTreeSet<String>) {
    fn target(t: &Expr, out: &mut std::collections::BTreeSet<String>) {
        match &t.kind {
            ExprKind::Name(n) => {
                out.insert(n.clone());
            }
            ExprKind::Tuple(xs) | ExprKind::List(xs) => xs.iter().for_each(|x| target(x, out)),
            ExprKind::Index(b, _) | ExprKind::Attr(b, _) => target(b, out),
            _ => {}
        }
    }
    for s in stmts {
        match &s.kind {
            StmtKind::Assign { targets, .. } => targets.iter().for_each(|t| target(t, out)),
            StmtKind::AugAssign { target: t, .. } | StmtKind::AnnAssign { target: t, .. } => target(t, out),
            StmtKind::If { body, orelse, .. } => {
                assigned(body, out);
                assigned(orelse, out);
            }
            StmtKind::Block { body, .. } | StmtKind::While { body, .. } | StmtKind::For { body, .. } => assigned(body, out),
            _ => {}
        }
    }
}

fn has_assert(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match &s.kind {
        StmtKind::Assert(_) => true,
        StmtKind::If { body, orelse, .. } => has_assert(body) || has_assert(orelse),
        StmtKind::Block { body, .. } => has_assert(body),
        _ => false,
    })
}

type Names = std::collections::BTreeSet<String>;

fn names_in(e: &Expr, out: &mut Names) {
    crate::expand::visit(e, &mut |x| {
        if let ExprKind::Name(n) = &x.kind {
            out.insert(n.clone());
        }
    });
}

/// What straight-line step code reads before writing it, and what it surely writes; `None`
/// for code this doesn't follow.
fn use_def(stmts: &[Stmt]) -> Option<(Names, Names)> {
    let (mut used, mut def) = (Names::new(), Names::new());
    let read = |e: &Expr, used: &mut Names, def: &Names| {
        let mut r = Names::new();
        names_in(e, &mut r);
        used.extend(r.into_iter().filter(|n| !def.contains(n)));
    };
    for s in stmts {
        match &s.kind {
            StmtKind::Pass => {}
            StmtKind::Expr(e) | StmtKind::Assert(e) => read(e, &mut used, &def),
            StmtKind::Assign { targets, value } => {
                read(value, &mut used, &def);
                let mut whole = Vec::new();
                for t in targets {
                    match &t.kind {
                        ExprKind::Name(n) => whole.push(n.clone()),
                        ExprKind::Tuple(xs) if xs.iter().all(|x| matches!(x.kind, ExprKind::Name(_))) => {
                            whole.extend(xs.iter().filter_map(|x| match &x.kind {
                                ExprKind::Name(n) => Some(n.clone()),
                                _ => None,
                            }))
                        }
                        // An element assignment keeps the other elements: it reads the array.
                        ExprKind::Index(..) => read(t, &mut used, &def),
                        _ => return None,
                    }
                }
                def.extend(whole);
            }
            StmtKind::AugAssign { target, value, .. } | StmtKind::AnnAssign { target, value: Some(value), .. } => {
                read(value, &mut used, &def);
                let ExprKind::Name(n) = &target.kind else { return None };
                if matches!(s.kind, StmtKind::AugAssign { .. }) && !def.contains(n) {
                    used.insert(n.clone());
                }
                def.insert(n.clone());
            }
            StmtKind::If { cond, body, orelse } => {
                read(cond, &mut used, &def);
                let (u1, d1) = use_def(body)?;
                let (u2, d2) = use_def(orelse)?;
                used.extend(u1.into_iter().chain(u2).filter(|n| !def.contains(n)));
                def.extend(d1.intersection(&d2).cloned());
            }
            _ => return None,
        }
    }
    Some((used, def))
}

/// Names live on entry to each step (read on some path before being written); `None` where
/// that can't be told (calls, returns, unusual code: anything might be read).
fn live_in(steps: &[Draft]) -> Vec<Option<Names>> {
    let local: Vec<Option<(Names, Names, Names)>> = steps
        .iter()
        .map(|d| {
            let (used, def) = use_def(&d.stmts)?;
            let mut term = Names::new();
            match &d.term {
                Term::Goto(_) | Term::Open => {}
                Term::Branch(e, ..) | Term::WaitUntil(e, _) | Term::WaitTicks(e, _) => names_in(e, &mut term),
                Term::Call(..) | Term::Return(_) => return None,
            }
            Some((used, def, term))
        })
        .collect();
    let mut live: Vec<Option<Names>> = vec![Some(Names::new()); steps.len()];
    loop {
        let mut changed = false;
        for i in (0..steps.len()).rev() {
            let new = local[i].as_ref().and_then(|(used, def, term)| {
                let mut out = term.clone();
                for t in targets(&steps[i].term).into_iter().flatten() {
                    out.extend(live[t].clone()?);
                }
                let mut l = used.clone();
                l.extend(out.into_iter().filter(|n| !def.contains(n)));
                Some(l)
            });
            if new != live[i] {
                live[i] = new;
                changed = true;
            }
        }
        if !changed {
            return live;
        }
    }
}

/// Profile-guided if-conversion of hot branch targets. A step ending in a branch that goes
/// one way most of the time (at least 2/3 of its runs, and `hot_min()` times or more) takes
/// in the code of that side: `A; if c → H else → O` becomes `A; t = c; if t: H`, continuing
/// where H continues (when `t`) or at O, so the hot path saves a step (two ticks or more)
/// and the cold path runs a longer step. The cold side is taken in too when that's needed to
/// keep two targets, if it is small. A side whose own branch condition is `d` computes it
/// in its arm (`t and d` in the merged condition). Sides that wait, call or return are left
/// alone.
///
/// When everything H writes is dead wherever the cold path continues, invisible outside the
/// process (`observable`), and H has no `assert` (and the build no `--checks`), H runs
/// unconditionally (speculatively) after the cold side's code, so its results don't pass
/// through selects on `t` (which would cost a tick: `if not t: d += 1` becomes `d + [not t]`).
/// Whether any of this pays off is decided by the caller ([`crate::compile`]), which costs
/// the whole build against the profile.
fn merge_hot_branches(steps: &mut [Draft], est: &mut Est, observable: &dyn Fn(&str) -> bool) {
    let n = steps.len();
    let mut budget = n;
    for a in 0..n {
        let Term::Branch(c, t, f) = steps[a].term.clone() else { continue };
        if t == f || budget == 0 {
            continue;
        }
        let (ct, cf) = (est.get(a, t), est.get(a, f));
        let hot_t = ct >= cf;
        let (hot, cold) = if hot_t { (t, f) } else { (f, t) };
        let hot_n = ct.max(cf);
        if hot_n < hot_min() || hot_n * 3.0 < (ct + cf) * 2.0 {
            continue;
        }
        let ok = |x: Target, cap: usize| match x {
            Some(i) if i != a => {
                matches!(steps[i].term, Term::Goto(_) | Term::Branch(..)) && steps[i].stmts.len() <= cap && !has_temp(&steps[i].stmts)
            }
            _ => false,
        };
        if !ok(hot, HOT_COPY) {
            continue;
        }
        let span = steps[a].span;
        let tmp = format!("#pgo{a}");
        let flag = name(&tmp, span);
        let not = |e: &Expr| Expr { kind: ExprKind::Not(Box::new(e.clone())), span: e.span };
        // A side's own branch condition is computed inside its arm of the `if` (into
        // `#pgo{a}t` or `…f`, False in the other arm), from the values on that path: read
        // after the `if`, it would see them through selects on the flag (deeper logic).
        let cond_tmp = |x: Target| format!("#pgo{a}{}", if x == t { "t" } else { "f" });
        // One side's ways out: (condition, target), the condition `None` when always.
        let outs = |x: Target, inlined: bool| -> Vec<(Option<Expr>, Target)> {
            match (inlined, x) {
                (true, Some(i)) => match &steps[i].term {
                    Term::Goto(y) => vec![(None, *y)],
                    Term::Branch(_, p, q) if p == q => vec![(None, *p)],
                    Term::Branch(_, p, q) => {
                        let d = name(&cond_tmp(x), span);
                        vec![(Some(d.clone()), *p), (Some(not(&d)), *q)]
                    }
                    _ => unreachable!(),
                },
                _ => vec![(None, x)],
            }
        };
        let combine = |inl_t: bool, inl_f: bool| -> Option<Term> {
            let sides = [(flag.clone(), outs(t, inl_t)), (not(&flag), outs(f, inl_f))];
            let mut targets: Vec<Target> = Vec::new();
            for (_, o) in &sides {
                for (_, y) in o {
                    if !targets.contains(y) {
                        targets.push(*y);
                    }
                }
            }
            match targets.len() {
                1 => Some(Term::Goto(targets[0])),
                2 => {
                    let p = targets[0];
                    let mut terms: Vec<Expr> = Vec::new();
                    for (sel, o) in &sides {
                        for (d, y) in o {
                            if *y == p {
                                terms.push(match d {
                                    None => sel.clone(),
                                    Some(d) => Expr { kind: ExprKind::BoolOp(ticky_syntax::ast::BoolOp::And, vec![sel.clone(), d.clone()]), span },
                                });
                            }
                        }
                    }
                    let cond = if terms.len() == 1 { terms.pop().unwrap() } else { Expr { kind: ExprKind::BoolOp(ticky_syntax::ast::BoolOp::Or, terms), span } };
                    Some(Term::Branch(cond, p, targets[1]))
                }
                _ => None,
            }
        };
        let (inl_t, inl_f, term) = match combine(hot_t, !hot_t) {
            Some(term) => (hot_t, !hot_t, term),
            None if ok(cold, MAX_COPY) => match combine(true, true) {
                Some(term) => (true, true, term),
                None => continue,
            },
            None => continue,
        };
        // Speculation: when everything the hot side writes is dead wherever the cold path
        // goes next (and nobody else can see it), the hot side's code runs unconditionally,
        // after the cold side's: no selects on the flag in front of its results.
        let h = hot.unwrap();
        // (Recomputed per merge: a merge changes what its step reads and writes.)
        let live = live_in(steps);
        let cold_next: Vec<Target> = if inl_t && inl_f { targets(&steps[cold.unwrap()].term) } else { vec![cold] };
        let spec = !crate::checks_on() && {
            let mut w = std::collections::BTreeSet::new();
            assigned(&steps[h].stmts, &mut w);
            !w.is_empty()
                && !has_assert(&steps[h].stmts)
                && w.iter().all(|n| !observable(n))
                && cold_next.iter().all(|c| c.is_none_or(|j| live[j].as_ref().is_some_and(|l| l.is_disjoint(&w))))
        };
        let arm = |x: Target, inl: bool| if inl && !(spec && x == hot) { steps[x.unwrap()].stmts.clone() } else { Vec::new() };
        let (mut body, mut orelse) = (arm(t, inl_t), arm(f, inl_f));
        let mut after = Vec::new();
        for (x, inl) in [(t, inl_t), (f, inl_f)] {
            let Some(i) = x.filter(|_| inl) else { continue };
            if spec && x == hot {
                after.extend(steps[i].stmts.clone());
                if let Term::Branch(d, p, q) = &steps[i].term {
                    if p != q {
                        after.push(assign(&cond_tmp(x), d.clone(), span));
                    }
                }
                continue;
            }
            if let Term::Branch(d, p, q) = &steps[i].term {
                if p != q {
                    let v = cond_tmp(x);
                    let (mine, other) = if x == t { (&mut body, &mut orelse) } else { (&mut orelse, &mut body) };
                    mine.push(assign(&v, d.clone(), span));
                    other.push(assign(&v, Expr { kind: ExprKind::Bool(false), span }, span));
                }
            }
        }
        steps[a].stmts.push(assign(&tmp, c.clone(), span));
        if !body.is_empty() || !orelse.is_empty() {
            steps[a].stmts.push(Stmt { kind: StmtKind::If { cond: flag.clone(), body, orelse }, span });
        }
        steps[a].stmts.extend(after);
        steps[a].term = term;
        budget -= 1;
        let arms: Vec<Target> = [(t, inl_t), (f, inl_f)].into_iter().filter(|(_, i)| *i).map(|(x, _)| x).collect();
        est.inline(a, &arms, false);
    }
}

/// A subroutine: name, return label and body.
pub type SubDef = (String, usize, Vec<Stmt>);

/// Builds the steps of process `proc` (`main` or its name: which profile applies).
///
/// `observable`: names something outside this process can see (ports, other processes'
/// and blocks' code), which profile-guided speculation must not write early.
pub fn build(proc: &str, stmts: &[Stmt], subs: &[SubDef], konst: &dyn Fn(&Expr) -> Option<i32>, observable: &dyn Fn(&str) -> bool) -> Result<Cfg, Diag> {
    let span = stmts.first().map(|s| s.span).unwrap_or_default();
    let mut b = Builder {
        steps: Vec::new(),
        cur: 0,
        loops: Vec::new(),
        labels: Default::default(),
        returns: Default::default(),
        hidden: Vec::new(),
        konst,
    };
    b.new_step(span);
    b.block(stmts)?;
    b.seal(Term::Goto(None));
    let mut sub_entry = std::collections::HashMap::new();
    for (name, label, body) in subs {
        let entry = b.new_step(body.first().map(|s| s.span).unwrap_or(span));
        sub_entry.insert(name.clone(), entry);
        b.returns.insert(*label, name.clone());
        b.cur = entry;
        b.block(body)?;
        b.seal(Term::Return(name.clone()));
    }
    let mut steps = b.steps;

    // Thread jumps through empty `goto` steps.
    let resolve = |steps: &[Draft], mut t: Target| -> Target {
        let mut hops = 0;
        while let Some(i) = t {
            match &steps[i].term {
                Term::Goto(next) if steps[i].stmts.is_empty() && hops < steps.len() => {
                    t = *next;
                    hops += 1;
                }
                _ => break,
            }
        }
        t
    };
    let snapshot = steps.clone();
    for d in &mut steps {
        retarget(&mut d.term, |t| resolve(&snapshot, t));
    }
    let entry = resolve(&snapshot, Some(0));
    for e in sub_entry.values_mut() {
        // A subroutine whose body is all empty jumps still needs a step to return from.
        if let Some(t) = resolve(&snapshot, Some(*e)) {
            *e = t;
        }
    }
    let protected: Vec<usize> = entry.into_iter().chain(sub_entry.values().copied()).collect();
    // Raw steps: what a profile counts (see `crate::profile`).
    let raw: Vec<RawStep> = steps
        .iter()
        .map(|d| RawStep { span: d.span, branch: match d.term { Term::Branch(_, t, f) => Some((t, f)), _ => None } })
        .collect();
    for (i, d) in steps.iter_mut().enumerate() {
        d.origin = vec![i];
    }
    // Profile-guided decisions (speed only: under `--opt=size` nothing is spent on ticks).
    let profile = if crate::opt_size() { None } else { crate::profile::for_proc(proc, &raw) };
    let mut est = profile.as_ref().map(Est::new);
    if let Some(e) = est.as_mut().filter(|_| crate::profile::guide().merge) {
        merge_hot_branches(&mut steps, e, observable);
    }
    fuse(&mut steps, &protected, est.as_mut());
    // Estimated runs of each step (what leaves it), to cost the decisions.
    if let Some(e) = &est {
        for (i, d) in steps.iter_mut().enumerate() {
            d.visits = e.outs(i).iter().map(|(_, n)| n).sum();
        }
    }
    if std::env::var_os("TICKY_DUMP_CFG").is_some() {
        eprintln!("== cfg of `{proc}` (profile: {})", profile.is_some());
        for (i, d) in steps.iter().enumerate() {
            eprintln!("step {i} origin {:?}: {} statements, {:?}", d.origin, d.stmts.len(), targets(&d.term));
            for s in &d.stmts {
                eprintln!("    {s:?}");
            }
        }
    }

    // Keep reachable steps only, renumbered in order.
    let mut keep = vec![false; steps.len()];
    let mut stack: Vec<usize> = entry.into_iter().collect();
    while let Some(i) = stack.pop() {
        if std::mem::replace(&mut keep[i], true) {
            continue;
        }
        stack.extend(targets(&steps[i].term).into_iter().flatten());
        if let Term::Call(f, _) = &steps[i].term {
            stack.push(sub_entry[f]);
        }
    }
    let mut new_id = vec![usize::MAX; steps.len()];
    let mut out = Vec::new();
    for (i, d) in steps.into_iter().enumerate() {
        if keep[i] {
            new_id[i] = out.len();
            out.push(d);
        }
    }
    for d in &mut out {
        retarget(&mut d.term, |t| t.map(|i| new_id[i]));
    }
    // A program whose code is all empty jumps still needs one (halting) step.
    let entry = match entry {
        Some(e) => new_id[e],
        None => {
            out.push(Draft { stmts: vec![], term: Term::Goto(None), span, origin: Vec::new(), visits: 0.0 });
            out.len() - 1
        }
    };
    let subs = sub_entry.into_iter().filter(|(_, e)| keep[*e]).map(|(f, e)| (f, new_id[e])).collect();
    Ok(Cfg { steps: out, entry, subs, hidden: b.hidden, raw })
}

impl Cfg {
    /// Real successors, including calls into subroutines and returns to every caller.
    pub fn successors(&self, i: usize) -> Vec<usize> {
        match &self.steps[i].term {
            Term::Call(f, _) => vec![self.subs[f]],
            Term::Return(f) => self
                .steps
                .iter()
                .filter_map(|d| match &d.term {
                    Term::Call(g, cont) if g == f => *cont,
                    _ => None,
                })
                .collect(),
            t => targets(t).into_iter().flatten().collect(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn cfg(src: &str) -> Cfg {
        let m = ticky_syntax::parse(src).unwrap();
        build("main", &m.body, &[], &|e| match e.kind {
            ExprKind::Int(v) => Some(v as i32),
            _ => None,
        }, &|_| true)
        .unwrap()
    }

    #[test]
    fn simple_loop_is_one_step_per_iteration() {
        let c = cfg("a = 0\nb = 1\nfor i in range(10):\n    a, b = b, a + b\nx = a\n");
        // entry (init + test), body (loops to itself), exit.
        assert_eq!(c.steps.len(), 3);
        let Term::Branch(_, Some(t), _) = &c.steps[1].term else { panic!("{:?}", c.steps[1].term) };
        assert_eq!(*t, 1);
    }

    /// Builds `src` with a profile in which every branch went to its `else` side 100 times
    /// (and once the other way), merging hot targets, with `observable` names.
    fn guided(src: &str, observable: &dyn Fn(&str) -> bool) -> Cfg {
        use crate::profile::{Guide, ProcProfile, Profile};
        let raw = cfg(src).raw;
        let mut edges = std::collections::BTreeMap::new();
        for (i, r) in raw.iter().enumerate() {
            if let Some((t, f)) = r.branch {
                edges.insert((i, t), 1);
                edges.insert((i, f), 100);
            }
        }
        let p = ProcProfile { steps: raw.iter().map(|r| (r.span, 0)).collect(), edges };
        let profile = Profile { source: 0, procs: [("main".to_string(), p)].into_iter().collect() };
        crate::profile::set_current(Some(profile), Guide { merge: true, copy: false });
        let m = ticky_syntax::parse(src).unwrap();
        let c = build("main", &m.body, &[], &|e| match e.kind {
            ExprKind::Int(v) => Some(v as i32),
            _ => None,
        }, observable);
        crate::profile::set_current(None, Guide { merge: false, copy: false });
        c.unwrap()
    }

    #[test]
    fn hot_branch_targets_merge_and_speculate_only_unseen_dead_writes() {
        // `d += 1` (the hot side) is dead after the `break` (the cold side), `probe` is not
        // dead if something outside can see it.
        let src = "d = 2\nwhile d < n:\n    if n % d == 0:\n        first = d\n        break\n    d += 1\n    probe = d\nx = d * 0\n";
        let stmt_names = |s: &Stmt| -> Vec<String> {
            let mut w = std::collections::BTreeSet::new();
            assigned(std::slice::from_ref(s), &mut w);
            w.into_iter().collect()
        };
        // The merged `if n % d == 0` step (it computes a flag `#pgo…` and assigns `first`).
        // What it writes outside its `if` runs unconditionally.
        let merged = |c: &Cfg| -> usize {
            c.steps.iter().position(|d| has_temp(&d.stmts) && {
                let mut w = std::collections::BTreeSet::new();
                assigned(&d.stmts, &mut w);
                w.contains("first")
            }).expect("a merged step")
        };
        let top_level = |c: &Cfg| -> Vec<String> {
            let d = &c.steps[merged(c)];
            d.stmts.iter().filter(|s| !matches!(s.kind, StmtKind::If { .. })).flat_map(stmt_names).filter(|n| !n.starts_with('#')).collect()
        };
        // `x = d * 0` reads `d` after the loop: nothing can be speculated.
        assert_eq!(top_level(&guided(src, &|_| false)), Vec::<String>::new());
        let src = src.replace("x = d * 0", "x = 1");
        assert_eq!(top_level(&guided(&src, &|_| false)), vec!["d".to_string(), "probe".to_string()]);
        // `probe` visible (an output, or read by another process): the hot side stays
        // conditional.
        assert_eq!(top_level(&guided(&src, &|n| n == "probe")), Vec::<String>::new());
        // The loop is one step now: the merged step branches back to itself.
        let c = guided(&src, &|_| false);
        let i = merged(&c);
        assert!(targets(&c.steps[i].term).contains(&Some(i)));
    }

    #[test]
    fn waits_and_breaks() {
        let c = cfg("while True:\n    wait until x > 0\n    y = 1\n    if x > 5:\n        break\n    wait 3\n");
        assert!(c.steps.iter().any(|d| matches!(d.term, Term::WaitUntil(..))));
        assert!(c.steps.iter().any(|d| matches!(d.term, Term::WaitTicks(..))));
    }
}
