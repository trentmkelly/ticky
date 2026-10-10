//! Sequential code → control-flow graph of *steps*. A step is straight-line code (simple `if`s
//! stay inside it and become selects) followed by one terminator. Each step becomes one state
//! of the process's state machine.
//!
//! Loops are rotated: the loop test is evaluated at the end of the step before the loop and at
//! the end of the body, so an iteration of a simple loop is a single step.

use ticky_syntax::ast::{BinOp, CmpOp, Expr, ExprKind, Stmt, StmtKind};
use ticky_syntax::{Diag, Span};

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
}

pub struct Cfg {
    pub steps: Vec<Draft>,
    pub entry: usize,
    /// Entry step of each subroutine.
    pub subs: std::collections::HashMap<String, usize>,
    /// Hidden variables introduced for `for` loops.
    pub hidden: Vec<String>,
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

impl Builder<'_> {
    fn new_step(&mut self, span: Span) -> usize {
        self.steps.push(Draft { stmts: Vec::new(), term: Term::Open, span });
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
                if is_simple(std::slice::from_ref(s)) {
                    let mut budget = 200_000;
                    let flat = crate::expand::flatten(vec![s.clone()], &mut budget)?;
                    self.steps[self.cur].stmts.extend(flat);
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
                if is_simple(std::slice::from_ref(s)) {
                    let mut budget = 200_000;
                    let flat = crate::expand::flatten(vec![s.clone()], &mut budget)?;
                    self.steps[self.cur].stmts.extend(flat);
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
        let id = self.hidden.len();
        let k = format!("{var}#k{id}");
        self.hidden.push(k.clone());
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
        self.steps[b].stmts.push(assign(var, name(&k, sp), sp));
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
fn fuse(steps: &mut [Draft], protected: &[usize]) {
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
            if !only && (steps[b].stmts.len() > MAX_COPY || budget == 0) {
                continue;
            }
            if !only {
                budget -= 1;
            }
            let (stmts, term) = (steps[b].stmts.clone(), steps[b].term.clone());
            steps[a].stmts.extend(stmts);
            steps[a].term = term;
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

/// A subroutine: name, return label and body.
pub type SubDef = (String, usize, Vec<Stmt>);

pub fn build(stmts: &[Stmt], subs: &[SubDef], konst: &dyn Fn(&Expr) -> Option<i32>) -> Result<Cfg, Diag> {
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
    fuse(&mut steps, &protected);

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
            out.push(Draft { stmts: vec![], term: Term::Goto(None), span });
            out.len() - 1
        }
    };
    let subs = sub_entry.into_iter().filter(|(_, e)| keep[*e]).map(|(f, e)| (f, new_id[e])).collect();
    Ok(Cfg { steps: out, entry, subs, hidden: b.hidden })
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
        build(&m.body, &[], &|e| match e.kind {
            ExprKind::Int(v) => Some(v as i32),
            _ => None,
        })
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

    #[test]
    fn waits_and_breaks() {
        let c = cfg("while True:\n    wait until x > 0\n    y = 1\n    if x > 5:\n        break\n    wait 3\n");
        assert!(c.steps.iter().any(|d| matches!(d.term, Term::WaitUntil(..))));
        assert!(c.steps.iter().any(|d| matches!(d.term, Term::WaitTicks(..))));
    }
}
