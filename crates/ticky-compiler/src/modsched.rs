//! Overlapping loop iterations (software pipelining) for loops whose body is one step
//! (PLAN.md §7, `--opt=speed` only).
//!
//! A loop iteration is one step, lasting its logic depth + 1 ticks. Part of that logic often
//! depends only on values that are already known one iteration earlier: names the loop
//! doesn't change, *induction variables* (`k += 1`), and variables the loop changes but
//! hasn't changed yet at that point of the body. `xs[k + 1]`'s index, `(start + k) * (start +
//! k)`, the loop test `k < n` after `k += 1`. Such a value can be computed while the previous
//! iteration runs, into a hidden register: iteration i+1's part of the work overlaps
//! iteration i (a modulo schedule with an initiation interval of one step).
//!
//! For a loop step `L` (it branches to itself) with predecessors `P`:
//!
//! - **Ahead registers.** An induction variable `v` (assigned in `L` only by one top-level
//!   `v += k`, `k` constant) gets `#m…a_d` holding `v + d·k`: what `v` will be `d` iterations
//!   later. `P` sets it (`= v + d·k`, part of the prologue), `L` adds `k`.
//! - **Early values.** An expression in `L` is *early* when it reads only constants, names `L`
//!   doesn't assign, induction variables, variables `L` assigns but hasn't assigned yet where
//!   the expression is read, and temporaries `t = early` assigned once at the top level of
//!   `L` (and not read before). Nothing anything outside the process can see, and only pure
//!   operations. Its value in iteration i is `F(Sᵢ)`, a pure function of the state `Sᵢ` at
//!   the start of the iteration (`v` read after its increment is `v + k`). The largest early
//!   subexpressions that do any work are replaced by a hidden register `#m…s`, which `P` sets
//!   to `F(S₀)` (the prologue) and `L` sets to `F(Sᵢ₊₁)` at the end of iteration i: from the
//!   ahead registers (`v ↦ a_1`, `v + k ↦ a_2`, registers, so no deeper than `F`), the
//!   variables' new values at the end of the body, and the unchanged names. (A value that
//!   reads nothing the loop changes is loop-invariant: only `P` computes it.)
//! - **The loop test** is read on the commit tick after everything else: when it contains
//!   early values, it is computed into a temporary `#m…c` before the new `#m…s` values are
//!   written, so it reads this iteration's.
//!
//! A round can be applied again: round 2 computes the operands of round 1's `#m…s = F` one
//! more iteration early, so `F`'s own depth drops to one combinator (stage count 3), and so
//! on.
//!
//! **Why it is invisible.** Every statement of the original body stays in its step, in the
//! same order, reading the same values: by induction over iterations, `#m…s` holds `F(Sᵢ)`
//! at the start of iteration i (set by `P` for i = 0, and by iteration i − 1 after, because
//! `F` is pure and what it reads at the end of iteration i − 1 is `Sᵢ`'s: the unchanged names
//! are unchanged, the other variables have their new values, `a_d = v(Sᵢ₋₁) + d·k = v(Sᵢ) +
//! (d − 1)·k`). What moves is only the computation of hidden registers, which no port, screen
//! or other process reads; early values never read inputs, other processes' variables or
//! `ticks()`, so nothing is sampled at another time. The value computed for the iteration
//! after the last one (and the prologue in a `P` that doesn't enter the loop) goes to a hidden
//! register nobody reads again: no iteration started past the exit commits anything
//! visible. Under `--checks`, early values contain no operation that can fail (division,
//! modulo, array reads), so a speculative one never raises an error. Steps get shorter or
//! longer, which SPEC §9.1 leaves to the compiler.
//!
//! **Whether to do it** is measured, not guessed ([`choose`]): the program is analysed
//! without the transformation and with one more round on every candidate loop; a loop keeps
//! a round only when its step got shorter and the predecessors' extra ticks are paid back
//! within [`GUESS_ITERS`] iterations per entry (the gain would be weighed by the profile's
//! counts, but the pass is off in profiled builds for now, see [`enabled`]). Hidden
//! registers are `int`s: a value that turns out to be a bundle or a signal is excluded and
//! the round tried again. `TICKY_NO_MODSCHED=1` turns the pass off,
//! `TICKY_DUMP_MODSCHED=1` prints the decisions, `TICKY_MODSCHED_FORCE=n` applies n rounds
//! everywhere, paying or not (for fuzzing).

use std::cell::RefCell;
use std::collections::{BTreeMap, BTreeSet, HashMap};

use ticky_syntax::ast::{BinOp, Expr, ExprKind, Stmt, StmtKind};
use ticky_syntax::{Diag, Span};

use crate::cfg::{Draft, Term};
use crate::program::{Program, StepKind};

/// Most rounds (pipeline stages beyond the first) per loop.
const MAX_ROUNDS: u32 = 3;
/// Without a profile: iterations per entry a loop is assumed to run when weighing a shorter
/// loop step against longer predecessors.
pub const GUESS_ITERS: f64 = 4.0;

/// A loop: its process and its step's raw steps (`Draft::origin`), the same in every
/// analysis of one program.
pub type Key = (String, Vec<usize>);

/// What to do with one loop.
#[derive(Clone, Default, PartialEq, Debug)]
struct LoopPlan {
    rounds: u32,
    /// Values (by [`key`]) not to compute early.
    exclude: BTreeSet<String>,
}

thread_local! {
    static PLAN: RefCell<HashMap<Key, LoopPlan>> = RefCell::new(HashMap::new());
    /// Loops found with something to pipeline, during the last analysis.
    static FOUND: RefCell<BTreeSet<Key>> = const { RefCell::new(BTreeSet::new()) };
    /// Registers made during the last analysis: name → (loop, value key).
    static REGS: RefCell<HashMap<String, (Key, String)>> = RefCell::new(HashMap::new());
    /// Off for this thread (tests compare against builds without the pass).
    static OFF: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Turns the pass off (or back on) for compilations on this thread.
pub fn set_disabled(off: bool) {
    OFF.with(|c| c.set(off));
}

/// On under `--opt=speed`, but not (yet) together with a profile: on `examples/primes.ticky`
/// it would take the profile-guided loop from 3 to 2 ticks per iteration (test 1111 → 875
/// ticks), but `tests/profile_guided.rs` pins the profiled build's 3 ticks.
fn enabled() -> bool {
    !crate::opt_size() && !crate::profile::active() && !OFF.with(|c| c.get()) && std::env::var_os("TICKY_NO_MODSCHED").is_none()
}

fn dump() -> bool {
    std::env::var_os("TICKY_DUMP_MODSCHED").is_some()
}

fn name(n: &str, span: Span) -> Expr {
    Expr { kind: ExprKind::Name(n.to_string()), span }
}

fn int(v: i64, span: Span) -> Expr {
    Expr { kind: ExprKind::Int(v), span }
}

fn assign(target: &str, value: Expr, span: Span) -> Stmt {
    Stmt { kind: StmtKind::Assign { targets: vec![name(target, span)], value }, span }
}

/// The expression without its source positions, as a key for equal expressions.
fn key(e: &Expr) -> String {
    strip_spans(&format!("{:?}", e.kind))
}

fn strip_spans(s: &str) -> String {
    let mut out = String::with_capacity(s.len());
    let mut rest = s;
    while let Some(i) = rest.find("span: Span {") {
        out.push_str(&rest[..i]);
        rest = &rest[i..];
        rest = &rest[rest.find('}').map_or(rest.len(), |j| j + 1)..];
    }
    out.push_str(rest);
    out
}

/// How often each name is assigned in `stmts` (anywhere; an element or attribute
/// assignment assigns the whole variable).
fn count_assigns(stmts: &[Stmt], out: &mut HashMap<String, usize>) {
    fn target(t: &Expr, out: &mut HashMap<String, usize>) {
        match &t.kind {
            ExprKind::Name(n) => *out.entry(n.clone()).or_insert(0) += 1,
            ExprKind::Tuple(xs) | ExprKind::List(xs) => xs.iter().for_each(|x| target(x, out)),
            ExprKind::Index(b, _) | ExprKind::Attr(b, _) => target(b, out),
            // Anything else: make sure nothing it might name looks unchanged.
            _ => crate::expand::visit(t, &mut |x| {
                if let ExprKind::Name(n) = &x.kind {
                    *out.entry(n.clone()).or_insert(0) += 2;
                }
            }),
        }
    }
    for s in stmts {
        match &s.kind {
            StmtKind::Assign { targets, .. } => targets.iter().for_each(|t| target(t, out)),
            StmtKind::AugAssign { target: t, .. } | StmtKind::AnnAssign { target: t, .. } => target(t, out),
            StmtKind::If { body, orelse, .. } => {
                count_assigns(body, out);
                count_assigns(orelse, out);
            }
            StmtKind::Block { body, .. } | StmtKind::While { body, .. } | StmtKind::For { body, .. } => count_assigns(body, out),
            _ => {}
        }
    }
}

fn assigned_by(s: &Stmt) -> impl Iterator<Item = String> {
    let mut a = HashMap::new();
    count_assigns(std::slice::from_ref(s), &mut a);
    a.into_keys()
}

/// Names `stmts` read (anywhere, including targets' indices).
fn reads(stmts: &[Stmt], out: &mut BTreeSet<String>) {
    let e = |x: &Expr, out: &mut BTreeSet<String>| {
        crate::expand::visit(x, &mut |y| {
            if let ExprKind::Name(n) = &y.kind {
                out.insert(n.clone());
            }
        })
    };
    for s in stmts {
        match &s.kind {
            StmtKind::Assign { targets, value } => {
                for t in targets {
                    if !matches!(t.kind, ExprKind::Name(_)) {
                        e(t, out);
                    }
                }
                e(value, out);
            }
            StmtKind::AugAssign { target, value, .. } => {
                e(target, out);
                e(value, out);
            }
            StmtKind::AnnAssign { value: Some(v), .. } => e(v, out),
            StmtKind::Expr(x) | StmtKind::Assert(x) => e(x, out),
            StmtKind::If { cond, body, orelse } => {
                e(cond, out);
                reads(body, out);
                reads(orelse, out);
            }
            StmtKind::AnnAssign { value: None, .. } | StmtKind::Pass => {}
            // Not in a step's code; treat as reading everything it mentions.
            _ => {
                let mut m = BTreeSet::new();
                crate::liveness::mentioned(std::slice::from_ref(s), &mut m);
                out.extend(m);
            }
        }
    }
}

/// Whether `stmts` are code this pass understands (what a step holds after if-conversion).
fn plain(stmts: &[Stmt]) -> bool {
    stmts.iter().all(|s| match &s.kind {
        StmtKind::Assign { .. } | StmtKind::AugAssign { .. } | StmtKind::AnnAssign { .. } | StmtKind::Expr(_) | StmtKind::Assert(_) | StmtKind::Pass => true,
        StmtKind::If { body, orelse, .. } => plain(body) && plain(orelse),
        _ => false,
    })
}

/// An induction variable of the loop being transformed.
struct Induction {
    var: String,
    /// What it is: the loop's base induction variable `base` (in [`Aheads`]), `off`
    /// iterations ahead (an earlier round's ahead register, or the variable itself).
    base: usize,
    off: i64,
}

/// A loop's ahead registers, shared by its rounds: `a{b}_{d}` holds base induction variable
/// `b` (`bases[b]`: name, step) `d` iterations ahead.
#[derive(Default)]
struct Aheads {
    /// Name prefix (the loop's).
    pfx: String,
    bases: Vec<(String, i64)>,
    /// Registers made so far → (base, distance).
    made: HashMap<String, (usize, i64)>,
}

impl Aheads {
    fn name(&self, b: usize, d: i64) -> String {
        format!("{}a{b}_{d}", self.pfx)
    }

    /// Variable `var`, an induction variable stepping by `step`: (base, offset).
    fn resolve(&mut self, var: &str, step: i64) -> (usize, i64) {
        if let Some(&(b, d)) = self.made.get(var).filter(|(b, _)| self.bases[*b].1 == step) {
            return (b, d);
        }
        let b = self.bases.iter().position(|x| x.0 == var && x.1 == step).unwrap_or_else(|| {
            self.bases.push((var.to_string(), step));
            self.bases.len() - 1
        });
        (b, 0)
    }
}

/// An early value: how to compute it at the loop's entry (from the real names, `v + k` for
/// an induction variable read after its increment) and for the next iteration at the end of
/// this one (from the ahead registers and the variables' new values), which ahead registers
/// (induction variable, distance) that needs, and whether it changes between iterations.
#[derive(Clone)]
struct Early {
    entry: Expr,
    next: Expr,
    aheads: BTreeSet<(usize, i64)>,
    varies: bool,
}

struct Loop<'a> {
    konst: &'a dyn Fn(&Expr) -> Option<i32>,
    observable: &'a dyn Fn(&str) -> bool,
    /// Names the step assigns, with counts.
    assigns: HashMap<String, usize>,
    inductions: Vec<Induction>,
    /// Early temporaries (`t = early`, once, at the top level, not read before).
    temps: HashMap<String, Early>,
    /// Name prefix of this round's registers.
    pfx: String,
    /// Registers made in this round: (value key, register, value).
    regs: Vec<(String, String, Early)>,
    /// Earlier rounds' value registers (round ≥ 2 splits their values).
    split: BTreeSet<String>,
    exclude: BTreeSet<String>,
    /// Names of the loop's ahead registers, by (base, distance).
    ahead_name: &'a dyn Fn(usize, i64) -> String,
    /// Steps of the base induction variables.
    steps: Vec<i64>,
}

impl Loop<'_> {
    /// The early form of `e`, read after the step's statements have assigned `done` (`end`:
    /// in the loop test, after all of them), if it is early.
    fn early(&self, e: &Expr, done: &BTreeSet<String>, end: bool) -> Option<Early> {
        let sp = e.span;
        let rebuild = |kids: Vec<&Expr>, mk: &dyn Fn(Vec<Expr>) -> ExprKind| -> Option<Early> {
            let (mut entry, mut next, mut aheads, mut varies) = (Vec::new(), Vec::new(), BTreeSet::new(), false);
            for k in kids {
                let x = self.early(k, done, end)?;
                entry.push(x.entry);
                next.push(x.next);
                aheads.extend(x.aheads);
                varies |= x.varies;
            }
            Some(Early { entry: Expr { kind: mk(entry), span: sp }, next: Expr { kind: mk(next), span: sp }, aheads, varies })
        };
        let same = |e: &Expr, varies: bool| Some(Early { entry: e.clone(), next: e.clone(), aheads: BTreeSet::new(), varies });
        let checks = crate::checks_on();
        match &e.kind {
            ExprKind::Int(_) | ExprKind::Bool(_) => same(e, false),
            ExprKind::Name(n) => {
                if (self.observable)(n) {
                    return None;
                }
                if let Some(ind) = self.inductions.iter().find(|d| &d.var == n) {
                    // `v` itself, or `v + k` after its increment; for the next iteration, the
                    // ahead register 1 or 2 iterations further on.
                    let after = end || done.contains(n);
                    let d = ind.off + if after { 2 } else { 1 };
                    let step = self.steps[ind.base];
                    let entry = if after { Expr { kind: ExprKind::Binary(BinOp::Add, Box::new(e.clone()), Box::new(int(step, sp))), span: sp } } else { e.clone() };
                    return Some(Early { entry, next: name(&(self.ahead_name)(ind.base, d), sp), aheads: [(ind.base, d)].into_iter().collect(), varies: true });
                }
                if let Some(t) = self.temps.get(n) {
                    return (end || done.contains(n)).then(|| t.clone());
                }
                match self.assigns.contains_key(n) {
                    // Unchanged by the loop.
                    false => same(e, false),
                    // Changed, but not yet: its value at the start of the iteration, which for
                    // the next one is its new value at the end of this one.
                    true if !end && !done.contains(n) => same(e, true),
                    true => None,
                }
            }
            ExprKind::Unary(op, a) => rebuild(vec![a], &|v| ExprKind::Unary(*op, Box::new(v[0].clone()))),
            ExprKind::Not(a) => rebuild(vec![a], &|v| ExprKind::Not(Box::new(v[0].clone()))),
            ExprKind::Binary(op, a, b) => {
                // Under `--checks` these can fail: never run speculatively.
                if checks && matches!(op, BinOp::Div | BinOp::FloorDiv | BinOp::Mod | BinOp::Pow) {
                    return None;
                }
                rebuild(vec![a, b], &|v| ExprKind::Binary(*op, Box::new(v[0].clone()), Box::new(v[1].clone())))
            }
            ExprKind::Compare(a, rest) => {
                let mut kids = vec![&**a];
                kids.extend(rest.iter().map(|(_, x)| x));
                let ops: Vec<_> = rest.iter().map(|(o, _)| *o).collect();
                rebuild(kids, &|v| ExprKind::Compare(Box::new(v[0].clone()), ops.iter().copied().zip(v[1..].iter().cloned()).collect()))
            }
            ExprKind::BoolOp(op, items) => rebuild(items.iter().collect(), &|v| ExprKind::BoolOp(*op, v)),
            ExprKind::IfExp { cond, then, orelse } => rebuild(vec![cond, then, orelse], &|v| ExprKind::IfExp {
                cond: Box::new(v[0].clone()),
                then: Box::new(v[1].clone()),
                orelse: Box::new(v[2].clone()),
            }),
            ExprKind::Call { func, args, kwargs } if kwargs.is_empty() => {
                let ExprKind::Name(f) = &func.kind else { return None };
                let pure = matches!(f.as_str(), "min" | "max" | "abs" | "clamp" | "int" | "bool")
                    || !checks && matches!(f.as_str(), "tdiv" | "tmod" | "#aget" | "#select" | "#ixok");
                // `min(xs)` of an array or bundle is a reduction: only the scalar forms.
                if !pure || matches!(f.as_str(), "min" | "max") && args.len() < 2 {
                    return None;
                }
                let func = func.clone();
                rebuild(args.iter().collect(), &|v| ExprKind::Call { func: func.clone(), args: v, kwargs: vec![] })
            }
            _ => None,
        }
    }

    /// Whether computing `x` early saves anything: it does some work (not a name or a
    /// constant).
    fn worth(&self, x: &Early) -> bool {
        !matches!(x.entry.kind, ExprKind::Name(_) | ExprKind::Int(_) | ExprKind::Bool(_))
            && (self.konst)(&x.entry).is_none()
            && !self.exclude.contains(&key(&x.entry))
    }

    fn reg_for(&mut self, x: Early) -> String {
        let k = key(&x.entry);
        if let Some((_, r, _)) = self.regs.iter().find(|(kk, _, _)| *kk == k) {
            return r.clone();
        }
        let r = format!("{}s{}", self.pfx, self.regs.len());
        self.regs.push((k, r.clone(), x));
        r
    }

    /// Replaces the largest early subexpressions of `e` (not `e` itself when `!root`).
    fn rewrite(&mut self, e: &mut Expr, done: &BTreeSet<String>, end: bool, root: bool) {
        if root {
            if let Some(x) = self.early(e, done, end).filter(|x| self.worth(x)) {
                let r = self.reg_for(x);
                *e = name(&r, e.span);
                return;
            }
        }
        match &mut e.kind {
            ExprKind::Unary(_, a) | ExprKind::Not(a) => self.rewrite(a, done, end, true),
            ExprKind::Binary(_, a, b) => {
                self.rewrite(a, done, end, true);
                self.rewrite(b, done, end, true);
            }
            ExprKind::Compare(a, rest) => {
                self.rewrite(a, done, end, true);
                for (_, x) in rest {
                    self.rewrite(x, done, end, true);
                }
            }
            ExprKind::BoolOp(_, items) => items.iter_mut().for_each(|x| self.rewrite(x, done, end, true)),
            ExprKind::IfExp { cond, then, orelse } => {
                self.rewrite(cond, done, end, true);
                self.rewrite(then, done, end, true);
                self.rewrite(orelse, done, end, true);
            }
            ExprKind::Call { args, .. } => args.iter_mut().for_each(|x| self.rewrite(x, done, end, true)),
            // Element reads in targets, tuples, comprehensions…: left alone.
            _ => {}
        }
    }

    /// Rewrites `stmts` in order; `done`: what earlier statements assigned (updated).
    fn rewrite_stmts(&mut self, stmts: &mut [Stmt], done: &mut BTreeSet<String>) {
        for s in stmts.iter_mut() {
            match &mut s.kind {
                StmtKind::Assign { targets, value } => {
                    // Round ≥ 2: an earlier round's `#m…s = F` keeps `F`'s top operation.
                    let root = !matches!(&targets[..], [Expr { kind: ExprKind::Name(n), .. }] if self.split.contains(n));
                    self.rewrite(value, done, false, root);
                }
                StmtKind::AugAssign { target, value, .. } => {
                    // An induction variable's own step is a constant.
                    if !matches!(&target.kind, ExprKind::Name(n) if self.inductions.iter().any(|d| &d.var == n)) {
                        self.rewrite(value, done, false, true);
                    }
                }
                StmtKind::AnnAssign { value: Some(v), .. } => self.rewrite(v, done, false, true),
                StmtKind::Expr(x) | StmtKind::Assert(x) => self.rewrite(x, done, false, true),
                StmtKind::If { cond, body, orelse } => {
                    self.rewrite(cond, done, false, true);
                    let (mut d1, mut d2) = (done.clone(), done.clone());
                    self.rewrite_stmts(body, &mut d1);
                    self.rewrite_stmts(orelse, &mut d2);
                    done.extend(d1);
                    done.extend(d2);
                    continue;
                }
                _ => {}
            }
            done.extend(assigned_by(s));
        }
    }
}

/// One round on loop step `l`: the registers made (value key, register), or `None` if there
/// was nothing to do.
#[allow(clippy::too_many_arguments)]
fn round(
    steps: &mut [Draft],
    l: usize,
    preds: &[usize],
    pfx: &str,
    split: &BTreeSet<String>,
    exclude: &BTreeSet<String>,
    ah: &mut Aheads,
    hidden: &mut Vec<String>,
    konst: &dyn Fn(&Expr) -> Option<i32>,
    observable: &dyn Fn(&str) -> bool,
) -> Option<Vec<(String, String)>> {
    let body = &steps[l].stmts;
    let mut assigns = HashMap::new();
    count_assigns(body, &mut assigns);
    let mut inductions = Vec::new();
    for s in body {
        if let StmtKind::AugAssign { target: Expr { kind: ExprKind::Name(v), .. }, op: op @ (BinOp::Add | BinOp::Sub), value } = &s.kind {
            if assigns.get(v) == Some(&1) && !observable(v) {
                if let Some(k) = konst(value).filter(|k| *k != 0) {
                    let step = if *op == BinOp::Add { k as i64 } else { -(k as i64) };
                    let (base, off) = ah.resolve(v, step);
                    inductions.push(Induction { var: v.clone(), base, off });
                }
            }
        }
    }
    let names = |b: usize, d: i64| format!("{}a{b}_{d}", ah.pfx);
    let mut lp = Loop {
        ahead_name: &names,
        steps: ah.bases.iter().map(|b| b.1).collect(),
        konst,
        observable,
        assigns,
        inductions,
        temps: HashMap::new(),
        pfx: pfx.to_string(),
        regs: Vec::new(),
        split: split.clone(),
        exclude: exclude.clone(),
    };
    // Early temporaries: `t = early`, once, at the top level, not read before.
    let mut done = BTreeSet::new();
    for (pos, s) in body.iter().enumerate() {
        if let StmtKind::Assign { targets, value } = &s.kind {
            if let [Expr { kind: ExprKind::Name(t), .. }] = &targets[..] {
                let mut before = BTreeSet::new();
                reads(&body[..pos], &mut before);
                if lp.assigns.get(t) == Some(&1) && !observable(t) && !before.contains(t) && !lp.inductions.iter().any(|d| &d.var == t) {
                    if let Some(x) = lp.early(value, &done, false) {
                        lp.temps.insert(t.clone(), x);
                    }
                }
            }
        }
        done.extend(assigned_by(s));
    }
    let mut stmts = steps[l].stmts.clone();
    lp.rewrite_stmts(&mut stmts, &mut BTreeSet::new());
    let mut term = steps[l].term.clone();
    let span = steps[l].span;
    let mut test = None;
    if let Term::Branch(c, t, f) = &term {
        let mut c2 = c.clone();
        lp.rewrite(&mut c2, &done, true, true);
        if key(&c2) != key(c) {
            let tmp = format!("{pfx}c");
            test = Some(assign(&tmp, c2, span));
            term = Term::Branch(name(&tmp, span), *t, *f);
        }
    }
    if lp.regs.is_empty() {
        return None;
    }
    // The kernel: this iteration's test, next iteration's early values (before any ahead
    // register's increment: they read this iteration's), the ahead registers' increments.
    let (regs, mut aheads) = (std::mem::take(&mut lp.regs), BTreeSet::new());
    drop(lp);
    let mut at = stmts
        .iter()
        .position(|s| matches!(&s.kind, StmtKind::AugAssign { target: Expr { kind: ExprKind::Name(n), .. }, .. } if ah.made.contains_key(n)))
        .unwrap_or(stmts.len());
    let mut kernel: Vec<Stmt> = test.into_iter().collect();
    let mut prologue = Vec::new();
    let mut made = Vec::new();
    for (k, r, x) in &regs {
        hidden.push(r.clone());
        made.push((k.clone(), r.clone()));
        prologue.push(assign(r, x.entry.clone(), span));
        // Unchanged by the loop: the prologue's value stays.
        if x.varies {
            kernel.push(assign(r, x.next.clone(), span));
            aheads.extend(x.aheads.iter().copied());
        }
    }
    for s in kernel {
        stmts.insert(at, s);
        at += 1;
    }
    for (b, d) in aheads {
        let a = ah.name(b, d);
        if ah.made.contains_key(&a) {
            continue;
        }
        ah.made.insert(a.clone(), (b, d));
        hidden.push(a.clone());
        let (var, step) = ah.bases[b].clone();
        let v = Expr { kind: ExprKind::Binary(BinOp::Add, Box::new(name(&var, span)), Box::new(int(d * step, span))), span };
        prologue.push(assign(&a, v, span));
        stmts.push(Stmt { kind: StmtKind::AugAssign { target: name(&a, span), op: BinOp::Add, value: int(step, span) }, span });
    }
    steps[l].stmts = stmts;
    steps[l].term = term;
    for &p in preds {
        steps[p].stmts.extend(prologue.iter().cloned());
    }
    Some(made)
}

fn targets(t: &Term) -> Vec<Option<usize>> {
    match t {
        Term::Open | Term::Return(_) => vec![],
        Term::Goto(a) | Term::WaitUntil(_, a) | Term::WaitTicks(_, a) | Term::Call(_, a) => vec![*a],
        Term::Branch(_, a, b) => vec![*a, *b],
    }
}

/// Register name prefix of a loop (`#m{loop}_`, in a process `P:#m{loop}_`), or of one of
/// its rounds (`#m{loop}_{round}`).
fn prefix(k: &Key, round: Option<u32>) -> String {
    let own = if k.0 == "main" { String::new() } else { format!("{}:", k.0) };
    format!("{own}#m{}_{}", k.1[0], round.map_or(String::new(), |r| r.to_string()))
}

/// Pipelines the loops of one process's steps (after step fusion) as the current plan says,
/// and records the loops that have something to pipeline. `proc`: `main` or the process's
/// name; `protected`: entry steps; `hidden`: gets the registers made.
pub fn transform(
    proc: &str,
    steps: &mut [Draft],
    protected: &[usize],
    hidden: &mut Vec<String>,
    konst: &dyn Fn(&Expr) -> Option<i32>,
    observable: &dyn Fn(&str) -> bool,
) {
    if !enabled() {
        return;
    }
    for l in 0..steps.len() {
        if !targets(&steps[l].term).contains(&Some(l)) || protected.contains(&l) || steps[l].origin.is_empty() || !plain(&steps[l].stmts) {
            continue;
        }
        // Every other way in must be a plain step (its code runs the prologue): no waits,
        // calls into the loop step or returns to it.
        let mut preds = Vec::new();
        let mut ok = true;
        for (p, d) in steps.iter().enumerate() {
            if p == l || !targets(&d.term).contains(&Some(l)) {
                continue;
            }
            ok &= matches!(d.term, Term::Goto(_) | Term::Branch(..)) && plain(&d.stmts);
            preds.push(p);
        }
        if !ok || preds.is_empty() {
            continue;
        }
        let key: Key = (proc.to_string(), steps[l].origin.clone());
        let plan = PLAN.with(|p| p.borrow().get(&key).cloned()).unwrap_or_default();
        if plan.rounds == 0 {
            // Only look: is there anything to pipeline?
            let mut copy: Vec<Draft> = steps.to_vec();
            let mut ah = Aheads { pfx: prefix(&key, None), ..Default::default() };
            if round(&mut copy, l, &preds, &prefix(&key, Some(0)), &BTreeSet::new(), &plan.exclude, &mut ah, &mut Vec::new(), konst, observable).is_some() {
                FOUND.with(|f| f.borrow_mut().insert(key));
            }
            continue;
        }
        let mut split = BTreeSet::new();
        let mut ah = Aheads { pfx: prefix(&key, None), ..Default::default() };
        for r in 0..plan.rounds {
            let Some(made) = round(steps, l, &preds, &prefix(&key, Some(r)), &split, &plan.exclude, &mut ah, hidden, konst, observable) else { break };
            for (k, reg) in made {
                REGS.with(|m| m.borrow_mut().insert(reg.clone(), (key.clone(), k)));
                split.insert(reg);
            }
        }
    }
}

/// For descriptions: what a register of this pass holds.
pub fn display(name: &str) -> Option<String> {
    let local = name.rsplit_once(':').map_or(name, |(_, l)| l);
    let rest = local.strip_prefix("#m")?;
    let (lp, reg) = rest.split_once('_')?;
    lp.parse::<usize>().ok()?;
    if let Some(a) = reg.strip_prefix('a') {
        let (_, d) = a.split_once('_')?;
        return Some(format!("pipelined loop counter, {d} ahead"));
    }
    let r = reg.trim_start_matches(|c: char| c.is_ascii_digit());
    match r.chars().next()? {
        's' => Some("pipelined value".into()),
        'c' => Some("pipelined loop test".into()),
        _ => None,
    }
}

/// Ticks of one run of a step that doesn't wait.
fn ticks(p: &Program, proc: usize, s: usize) -> u32 {
    let st = &p.procs[proc].steps[s];
    match st.kind {
        StepKind::Run(_) => st.depth.max(1) + 1,
        _ => st.wait_ready + 2,
    }
}

/// The loop's step in an analysis: (process, step).
fn find(p: &Program, k: &Key) -> Option<(usize, usize)> {
    let pi = p.procs.iter().position(|m| m.name == k.0)?;
    let l = p.procs[pi].steps.iter().enumerate().position(|(i, s)| s.origin == k.1 && s.targets().contains(&Some(i)))?;
    Some((pi, l))
}

/// A loop's cost in one analysis: (its step's ticks, its runs, the predecessors' (ticks,
/// runs)).
fn measure(p: &Program, k: &Key) -> Option<(u32, f64, Vec<(u32, f64)>)> {
    let (pi, l) = find(p, k)?;
    let m = &p.procs[pi];
    let preds = m.steps.iter().enumerate().filter(|(i, s)| *i != l && s.targets().contains(&Some(l))).map(|(i, s)| (ticks(p, pi, i), s.visits)).collect();
    Some((ticks(p, pi, l), m.steps[l].visits, preds))
}

/// The registers of the analysis that hold something other than a number (hidden registers
/// are `int` states: a bundle or a signal must not be computed early).
fn not_numbers(p: &Program) -> BTreeSet<String> {
    let mut bad = BTreeSet::new();
    for m in &p.procs {
        for (si, v) in m.steps.iter().flat_map(|s| &s.writes) {
            if crate::bundle::kind(&m.graph, *v) != crate::bundle::Kind::Int {
                let s = &p.states[*si];
                bad.extend(std::iter::once(&s.name).chain(&s.shared).filter(|n| n.contains("#m")).cloned());
            }
        }
    }
    bad
}

/// Whether the loop step's duration is set by what it still computes after dead stores are
/// pruned. (`program::prune_dead_stores` keeps a step's duration when it drops dead
/// arithmetic, so that removing it never moves a sample or an output; a loop that is only
/// that long because of dead code is left alone rather than pipelining code nobody reads.)
fn live_critical(p: &Program, k: &Key) -> bool {
    let Some((pi, l)) = find(p, k) else { return false };
    let (m, s) = (&p.procs[pi], &p.procs[pi].steps[l]);
    let depths = m.graph.depths();
    let ready = |nodes: Vec<crate::ir::V>| nodes.iter().map(|v| depths[*v as usize]).max().unwrap_or(0);
    let mut d = s.plans.iter().map(|(_, pl)| pl.ready(&depths)).max().unwrap_or(0);
    if !s.checks.is_empty() {
        d = d.max(ready(s.checks.iter().map(|c| c.fail).collect()) + 1);
    }
    if let StepKind::Run(crate::program::Next::Branch(c, ..)) = &s.kind {
        d = d.max(ready(crate::program::cond_operands(c, true)));
    }
    d.max(1) >= s.depth.max(1)
}

/// Expected ticks saved by going from `before` to `after` for loop `k` (positive: faster),
/// or why not.
fn gain(before: &Program, after: &Program, k: &Key) -> Result<f64, &'static str> {
    if !live_critical(before, k) {
        return Err("its step is that long only because of dead code");
    }
    let (l0, _, p0) = measure(before, k).ok_or("loop step not found")?;
    let (l1, runs, p1) = measure(after, k).ok_or("loop step not found")?;
    if p0.len() != p1.len() {
        return Err("predecessors changed");
    }
    if l1 >= l0 {
        return Err("no shorter step");
    }
    let profiled = runs > 0.0;
    let mut g = if profiled { runs * (l0 - l1) as f64 } else { GUESS_ITERS * (l0 - l1) as f64 };
    for (a, b) in p0.iter().zip(&p1) {
        let w = if profiled { b.1 } else { 1.0 };
        g -= w * (b.0 as f64 - a.0 as f64);
    }
    Ok(g)
}

fn set_plan(plan: &HashMap<Key, LoopPlan>) {
    PLAN.with(|p| *p.borrow_mut() = plan.clone());
}

/// Analyses with `plan`; registers that turn out not to be numbers are excluded from their
/// loop's plan (updated) and the analysis repeated.
fn analyze_with(plan: &mut HashMap<Key, LoopPlan>, analyze: &dyn Fn() -> Result<Program, Vec<Diag>>) -> Option<Program> {
    for _ in 0..4 {
        set_plan(plan);
        REGS.with(|m| m.borrow_mut().clear());
        let p = analyze().ok()?;
        let bad = not_numbers(&p);
        let regs = REGS.with(|m| m.borrow().clone());
        let mut changed = false;
        for b in &bad {
            if let Some((k, v)) = regs.get(b) {
                changed |= plan.get_mut(k).is_some_and(|lp| lp.exclude.insert(v.clone()));
            }
        }
        if !changed {
            // Anything still wrong (a register we can't trace): no.
            return (!bad.iter().any(|b| regs.contains_key(b))).then_some(p);
        }
    }
    None
}

/// Runs `analyze` (one whole analysis of the program) without pipelining, then with more
/// rounds for each loop while that pays (see the module docs), and returns the analysis of
/// the plan chosen.
pub fn choose(analyze: impl Fn() -> Result<Program, Vec<Diag>>) -> Result<Program, Vec<Diag>> {
    if !enabled() {
        return analyze();
    }
    let none = HashMap::new();
    set_plan(&none);
    FOUND.with(|f| f.borrow_mut().clear());
    let base = analyze();
    let found: Vec<Key> = FOUND.with(|f| std::mem::take(&mut *f.borrow_mut())).into_iter().collect();
    let Ok(base) = base else { return base };
    if found.is_empty() {
        return Ok(base);
    }
    // Testing: `TICKY_MODSCHED_FORCE=n` applies n rounds to every candidate, paying or not.
    if let Some(n) = std::env::var("TICKY_MODSCHED_FORCE").ok().and_then(|v| v.parse::<u32>().ok()) {
        let mut plan: HashMap<Key, LoopPlan> = found.iter().map(|k| (k.clone(), LoopPlan { rounds: n, ..Default::default() })).collect();
        let r = analyze_with(&mut plan, &analyze);
        set_plan(&none);
        return Ok(r.unwrap_or(base));
    }
    let mut plan: HashMap<Key, LoopPlan> = HashMap::new();
    // Each loop's accepted state was measured in `progs[at[k]]`.
    let mut progs: Vec<Program> = vec![base];
    let mut at: BTreeMap<Key, usize> = found.iter().map(|k| (k.clone(), 0)).collect();
    let mut active: Vec<Key> = found.clone();
    let mut last_plan = none.clone();
    for r in 1..=MAX_ROUNDS {
        if active.is_empty() {
            break;
        }
        let mut trial = plan.clone();
        for k in &active {
            trial.entry(k.clone()).or_default().rounds = r;
        }
        let mut batches: Vec<(usize, HashMap<Key, LoopPlan>, Vec<Key>)> = Vec::new();
        match analyze_with(&mut trial, &analyze) {
            Some(p) => {
                progs.push(p);
                batches.push((progs.len() - 1, trial.clone(), active.clone()));
            }
            // Some loop's round fails to compile: try them one at a time.
            None => {
                for k in &active {
                    let mut one = plan.clone();
                    one.entry(k.clone()).or_default().rounds = r;
                    if let Some(p) = analyze_with(&mut one, &analyze) {
                        progs.push(p);
                        batches.push((progs.len() - 1, one, vec![k.clone()]));
                    }
                }
            }
        }
        let mut next = Vec::new();
        for (idx, tried, keys) in &batches {
            last_plan = tried.clone();
            for k in keys {
                let g = gain(&progs[at[k]], &progs[*idx], k);
                if dump() {
                    eprintln!("[modsched] {} loop {:?} round {r}: {}", k.0, k.1, g.map_or_else(|e| e.to_string(), |g| format!("{g:+.1} ticks expected")));
                }
                if g.is_ok_and(|g| g > 0.0) {
                    plan.insert(k.clone(), tried[k].clone());
                    at.insert(k.clone(), *idx);
                    next.push(k.clone());
                }
            }
        }
        active = next;
    }
    if dump() {
        let mut v: Vec<_> = plan.iter().map(|(k, p)| (k, p.rounds, p.exclude.len())).collect();
        v.sort();
        eprintln!("[modsched] plan (loop, rounds, values excluded): {v:?}");
    }
    let result = if plan.is_empty() {
        progs.swap_remove(0)
    } else if plan == last_plan {
        progs.pop().unwrap()
    } else {
        let mut p = plan.clone();
        match analyze_with(&mut p, &analyze) {
            Some(x) => x,
            None => progs.swap_remove(0),
        }
    };
    set_plan(&none);
    Ok(result)
}

#[cfg(test)]
mod tests {
    use super::*;

    /// The steps of `src` (a main program) with `rounds` rounds on every loop.
    fn steps(src: &str, rounds: u32) -> crate::cfg::Cfg {
        let m = ticky_syntax::parse(src).unwrap();
        let konst = |e: &Expr| match e.kind {
            ExprKind::Int(v) => Some(v as i32),
            _ => None,
        };
        let observable = |n: &str| n == "out";
        // Find the loops, then plan them.
        set_plan(&HashMap::new());
        FOUND.with(|f| f.borrow_mut().clear());
        crate::cfg::build("main", &m.body, &[], &konst, &observable).unwrap();
        let found: HashMap<Key, LoopPlan> = FOUND.with(|f| f.borrow().iter().map(|k| (k.clone(), LoopPlan { rounds, ..Default::default() })).collect());
        set_plan(&found);
        let c = crate::cfg::build("main", &m.body, &[], &konst, &observable).unwrap();
        set_plan(&HashMap::new());
        c
    }

    /// Statements as short text (no positions).
    fn text(stmts: &[Stmt]) -> Vec<String> {
        stmts.iter().map(|s| strip_spans(&format!("{:?}", s.kind)).replace("Expr { kind: ", "").replace(", }", "").replace(" }", "")).collect()
    }

    fn loop_step(c: &crate::cfg::Cfg) -> usize {
        (0..c.steps.len()).find(|&i| targets(&c.steps[i].term).contains(&Some(i))).expect("a loop step")
    }

    #[test]
    fn early_values_move_to_the_previous_iteration_and_the_prologue() {
        // `out` is visible outside the process: never read early.
        let c = steps("k = 3\ns = 0\nfor i in range(10):\n    s += (i * i + k) * 7 + out\nr = s\n", 1);
        let l = loop_step(&c);
        let body = text(&c.steps[l].stmts);
        // The body adds the register (the read of `out` stays in place).
        assert!(body[1].contains("Name(\"#m") && body[1].contains("Name(\"out\")"), "{body:?}");
        assert!(!body[1].contains("Mul"), "{body:?}");
        // The test is taken before the new values are written; next iteration's value comes
        // from the ahead register, whose increment is last.
        let Term::Branch(cond, ..) = &c.steps[l].term else { panic!() };
        assert!(matches!(&cond.kind, ExprKind::Name(n) if n.ends_with('c')));
        let pos = |pat: &str| body.iter().position(|s| s.contains(pat)).unwrap_or_else(|| panic!("{pat} in {body:?}"));
        let value = pos("Assign { targets: [Name(\"#m1_0s0\")");
        assert!(pos("Assign { targets: [Name(\"#m1_0c\")") < value);
        assert!(value < pos("AugAssign { target: Name(\"#m1_a0_1\")"));
        assert!(body[value].contains("#m1_a0_1"), "{}", body[value]);
        // The step before the loop computes the first iteration's values.
        let pred = (0..c.steps.len())
            .find(|&p| p != l && text(&c.steps[p].stmts).iter().any(|s| s.starts_with("Assign { targets: [Name(\"#m1_a0_1\")")))
            .expect("prologue");
        assert!(targets(&c.steps[pred].term).contains(&Some(l)));
        assert!(c.hidden.iter().any(|h| h == "#m1_0s0") && c.hidden.iter().any(|h| h == "#m1_a0_1"));
    }

    #[test]
    fn later_rounds_split_values_and_share_ahead_registers() {
        let c = steps("s = 0\nfor i in range(10):\n    s += (i * 3 + 1) * (i * 5 - 2)\nr = s\n", 2);
        // Round 2 computes `i * 3 + 1` and `i * 5 - 2` one iteration earlier still, from `i`
        // two iterations ahead: the register round 1 made for the loop test.
        let regs: Vec<&String> = c.hidden.iter().filter(|h| h.starts_with("#m")).collect();
        assert_eq!(regs.iter().filter(|h| h.ends_with("_a0_2")).count(), 1, "{regs:?}");
        assert!(regs.iter().any(|h| h.starts_with("#m1_1s")), "{regs:?}");
    }

    #[test]
    fn variables_the_loop_changes_are_early_only_before_they_change() {
        // `x` is read before it changes (early), `y` after (not).
        let c = steps("x = 1\ny = 2\nfor i in range(5):\n    t = (x * 3 + 1) * 5\n    x = x + t\n    if x > 3:\n        y = y * 2\n    u = (y * 3 + 1) * 5\n    x = x + u\nr = x\n", 1);
        let body = text(&c.steps[loop_step(&c)].stmts);
        assert!(body.iter().any(|s| s.starts_with("Assign { targets: [Name(\"t\")") && s.contains("value: Name(\"#m")), "{body:?}");
        assert!(body.iter().any(|s| s.starts_with("Assign { targets: [Name(\"u\")") && s.contains("value: Binary(Mul")), "{body:?}");
    }

    #[test]
    fn names_for_descriptions() {
        assert_eq!(display("#m4_0s1").as_deref(), Some("pipelined value"));
        assert_eq!(display("p:#m12_a0_2").as_deref(), Some("pipelined loop counter, 2 ahead"));
        assert_eq!(display("#t4"), None);
        assert_eq!(display("xs#0"), None);
    }
}
