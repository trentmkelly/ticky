//! Semantic analysis: classifies every module-level name (port, constant, state), checks the
//! single-writer rule, and lowers `every` blocks and the sequential `main` process to IR.
//!
//! Top-level code is the `main` process. Its leading run of constant assignments (the
//! *prologue*) runs "before time starts": those become constants, or the initial values of
//! variables that are assigned again later.

use std::collections::{BTreeMap, BTreeSet, HashMap, HashSet};

use ticky_factorio::{Sig, SignalTable};
use ticky_syntax::ast::{Expr, ExprKind, Module, PortDir, SignalSpec, Stmt, StmtKind};
use ticky_syntax::{Diag, Span};

use crate::cfg::{self, Term};
use crate::fuse::{CondPlan, Fuser, WriterPlan};
use crate::ir::{BVals, Cv, Graph, Iv, SrcId, V};
use crate::lower::{self, Names};
use ticky_factorio::ArOp;

/// Owner id of the `main` process (every blocks are numbered from 0).
pub const MAIN: usize = usize::MAX;

/// Owner id of the `k`-th `process` (counting down from `MAIN`).
pub fn proc_owner(k: usize) -> usize {
    MAIN - 1 - k
}

/// Whether an owner id is a sequential process (`main` or a `process`), not an `every` block.
pub fn is_proc(owner: usize) -> bool {
    owner > usize::MAX / 2
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Ty {
    Int,
    Bool,
    Bundle,
    /// A runtime signal: carried as a one-hot bundle (that signal with value 1).
    Signal,
}

impl Ty {
    pub fn name(self) -> &'static str {
        match self {
            Ty::Int => "int",
            Ty::Bool => "bool",
            Ty::Bundle => "Bundle",
            Ty::Signal => "Signal",
        }
    }

    /// Carried as a bundle (on its own wires).
    pub fn is_bun(self) -> bool {
        matches!(self, Ty::Bundle | Ty::Signal)
    }
}

#[derive(Clone, Debug)]
pub struct Port {
    pub name: String,
    pub dir: PortDir,
    pub ty: Ty,
    /// The port's signal (`signal-each` for bundle ports, which carry every signal).
    pub sig: Sig,
    pub label: Option<String>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct State {
    pub name: String,
    pub ty: Ty,
    pub init: i32,
    /// Initial value of a bundle state.
    pub binit: BVals,
    /// Has an initial value from the prologue (or is an output, which starts at 0).
    pub has_init: bool,
    /// The process that assigns it (`MAIN` or an every-block index); `None` = never changes.
    pub owner: Option<usize>,
    /// Set for output ports.
    pub port: Option<usize>,
    pub span: Span,
    /// The variables renamed to this one by register sharing (they share its register).
    pub shared: Vec<String>,
}

impl State {
    /// For descriptions: the variable's name, or the names of all the variables sharing its
    /// register (`` `a` / `b` / `steps` ``).
    pub fn display_name(&self) -> String {
        std::iter::once(&self.name).chain(&self.shared).map(|n| Self::display_one(n)).collect::<Vec<_>>().join(" / ")
    }

    /// Hidden loop variables have names that can't be written in source.
    fn display_one(name: &str) -> String {
        if let Some(d) = crate::modsched::display(name) {
            return d;
        }
        if let Some((var, rest)) = name.split_once('#') {
            if rest.starts_with('k') || rest.starts_with("end") {
                return format!("loop counter for {}", crate::expand::display(var));
            }
        }
        match crate::expand::display(name) {
            d if d.starts_with('`') || d.starts_with("the ") || d.starts_with("a ") => d,
            d => format!("`{d}`"),
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum SrcKind {
    /// The process's own state register, read directly.
    Own(usize),
    /// An input port, sampled when an iteration/step starts.
    Input(usize),
    /// State owned by another process, sampled when an iteration/step starts.
    Foreign(usize),
    /// `ticks()`, sampled.
    Ticks,
    /// Unsampled versions, for `wait until` conditions.
    LiveInput(usize),
    LiveForeign(usize),
    LiveTicks,
}

/// A runtime check (`--checks`): fails when `fail` is true; reported as `code`.
#[derive(Clone, Debug)]
pub struct Check {
    pub fail: V,
    pub code: i32,
    pub span: Span,
    pub what: &'static str,
}

/// A check's source location and kind, for the build report (`Program::checks[code - 1]`).
pub struct CheckSite {
    pub span: Span,
    pub what: &'static str,
    /// `main`, the process's name or `every`.
    pub owner: String,
}

pub struct Block {
    pub span: Span,
    /// Runtime checks (`--checks`).
    pub checks: Vec<Check>,
    /// `every N ticks:`; `None` for `every tick:`.
    pub requested: Option<u32>,
    pub srcs: Vec<SrcKind>,
    pub graph: Graph,
    /// How each state this block owns is updated (states it never changes are absent).
    pub plans: Vec<(usize, WriterPlan)>,
    /// Longest combinator chain from sources to a next value.
    pub depth: u32,
    /// Ticks per iteration.
    pub period: u32,
    /// Set when the block runs every tick as a pipeline (instead of multi-cycle).
    pub pipe: Option<crate::pipeline::Pipe>,
}

#[derive(Clone, Debug, PartialEq)]
pub enum Next {
    /// `None` halts the process.
    Goto(Option<usize>),
    Branch(CondPlan, Option<usize>, Option<usize>),
    /// Jump to a subroutine's entry, recording `cont` as where it returns to.
    Call { func: String, entry: usize, cont: Option<usize> },
    /// Jump back to wherever the subroutine was called from.
    Return { func: String },
}

#[derive(Clone, Debug, PartialEq)]
pub enum WaitN {
    Const(i32),
    /// `n - 2`, compared against the step timer.
    Dyn(V),
}

#[derive(Clone, Debug, PartialEq)]
pub enum StepKind {
    Run(Next),
    WaitUntil(CondPlan, Option<usize>),
    WaitTicks(WaitN, Option<usize>),
}

#[derive(Clone, Debug)]
pub struct Step {
    pub span: Span,
    /// The raw steps it runs (`cfg::Draft::origin`), for profiles.
    pub origin: Vec<usize>,
    /// With a profile: estimated runs in the profiled run (`cfg::Draft::visits`).
    pub visits: f64,
    /// New values of the variables this step assigns.
    pub writes: Vec<(usize, V)>,
    /// How those writes are carried out (after fusion).
    pub plans: Vec<(usize, WriterPlan)>,
    pub kind: StepKind,
    /// Ticks after the step starts until everything committed at its end is ready.
    pub depth: u32,
    /// For waits: ticks after the step starts until the wait condition can be checked.
    pub wait_ready: u32,
    /// Runtime checks (`--checks`) in this step.
    pub checks: Vec<Check>,
}

/// Nodes a condition needs: its condition lists' operands, or the node itself.
pub fn cond_operands(c: &CondPlan, both: bool) -> Vec<V> {
    match (&c.pos, &c.neg) {
        (Some(p), Some(n)) => crate::ir::dnf_operands(p).chain(crate::ir::dnf_operands(n)).collect(),
        (Some(p), None) if !both => crate::ir::dnf_operands(p).collect(),
        _ => vec![c.node],
    }
}

impl Step {
    pub fn roots(&self) -> Vec<V> {
        let mut r: Vec<V> = self.plans.iter().flat_map(|(_, p)| p.operands()).collect();
        r.extend(self.checks.iter().map(|c| c.fail));
        match &self.kind {
            StepKind::Run(Next::Branch(c, ..)) => r.extend(cond_operands(c, true)),
            StepKind::WaitUntil(c, _) => r.extend(cond_operands(c, false)),
            StepKind::WaitTicks(WaitN::Dyn(m), _) => r.push(*m),
            _ => {}
        }
        r
    }

    /// Static successors (a call's continuation counts; returns have none).
    pub fn targets(&self) -> Vec<Option<usize>> {
        match &self.kind {
            StepKind::Run(Next::Goto(t)) | StepKind::WaitUntil(_, t) | StepKind::WaitTicks(_, t) => vec![*t],
            StepKind::Run(Next::Branch(_, a, b)) => vec![*a, *b],
            StepKind::Run(Next::Call { entry, cont, .. }) => vec![Some(*entry), *cont],
            StepKind::Run(Next::Return { .. }) => vec![],
        }
    }
}

pub struct MainProc {
    /// `main` or the process's name.
    pub name: String,
    /// Owner id of its variables (`MAIN` or [`proc_owner`]).
    pub owner: usize,
    pub srcs: Vec<SrcKind>,
    pub graph: Graph,
    pub steps: Vec<Step>,
    pub entry: usize,
    /// The raw steps (`cfg::Cfg::raw`), for profiles.
    pub raw: Vec<crate::profile::RawStep>,
}

impl MainProc {
    /// Sources reachable from emitted stores, checks and control flow. Original writes
    /// remain available for timing/debugging but do not keep dead samplers alive.
    pub fn used_sources(&self) -> BTreeSet<usize> {
        let roots: Vec<V> = self.steps.iter().flat_map(Step::roots).collect();
        self.graph.reachable(&roots).into_iter().filter_map(|v| match self.graph.op(v) {
            crate::ir::Op::Src(s) => Some(*s as usize),
            _ => None,
        }).collect()
    }
}

pub struct TestDef {
    pub name: String,
    pub span: Span,
    pub body: Vec<Stmt>,
}

pub struct Program {
    /// How many times each function is called (inlined, or as a subroutine).
    pub calls: std::collections::BTreeMap<String, usize>,
    /// Functions compiled once as subroutines.
    pub subroutines: std::collections::BTreeSet<String>,
    pub ports: Vec<Port>,
    pub states: Vec<State>,
    pub consts: HashMap<String, Cv>,
    pub blocks: Vec<Block>,
    /// Sequential processes: `main` (if there are top-level statements) first, then each
    /// `process` in file order.
    pub procs: Vec<MainProc>,
    pub tests: Vec<TestDef>,
    pub warnings: Vec<Diag>,
    /// Runtime checks (`--checks`), by code - 1.
    pub checks: Vec<CheckSite>,
    /// With `--checks`: the `error` output port (signal-E) carrying the first failed check's code.
    pub error_port: Option<usize>,
    /// Screens (`import display`): signal arrays shown on lamp grids.
    pub screens: Vec<crate::display::Screen>,
    /// Outputs and screens whose values may depend on random picks (`import random`).
    pub random: std::collections::HashSet<String>,
    /// Inputs fed by controls in the blueprint (`import controls`).
    pub controls: Vec<crate::stdlib::Control>,
}

impl Program {
    pub fn port_index(&self, name: &str) -> Option<usize> {
        self.ports.iter().position(|p| p.name == name)
    }

    pub fn output_state(&self, port: usize) -> Option<usize> {
        self.states.iter().position(|s| s.port == Some(port))
    }

    pub fn uses_ticks(&self) -> bool {
        let uses = |srcs: &[SrcKind]| srcs.iter().any(|s| matches!(s, SrcKind::Ticks | SrcKind::LiveTicks));
        self.blocks.iter().any(|b| uses(&b.srcs)) || self.procs.iter().any(|m| uses(&m.srcs))
    }
}

/// Every name assigned anywhere in `body`, with the first assignment's span.
fn assigned_names(body: &[Stmt], out: &mut BTreeMap<String, Span>, errs: &mut Vec<Diag>) {
    fn target(e: &Expr, out: &mut BTreeMap<String, Span>, errs: &mut Vec<Diag>) {
        match &e.kind {
            ExprKind::Name(n) => {
                out.entry(n.clone()).or_insert(e.span);
            }
            ExprKind::Tuple(items) => items.iter().for_each(|i| target(i, out, errs)),
            _ => errs.push(Diag::error(e.span, "can only assign to names here")),
        }
    }
    for s in body {
        match &s.kind {
            StmtKind::Assign { targets, .. } => targets.iter().for_each(|t| target(t, out, errs)),
            StmtKind::AugAssign { target: t, .. } | StmtKind::AnnAssign { target: t, .. } => target(t, out, errs),
            StmtKind::For { target: t, body, .. } => {
                target(t, out, errs);
                assigned_names(body, out, errs);
            }
            StmtKind::If { body, orelse, .. } => {
                assigned_names(body, out, errs);
                assigned_names(orelse, out, errs);
            }
            StmtKind::While { body, .. } | StmtKind::Block { body, .. } => assigned_names(body, out, errs),
            _ => {}
        }
    }
}

/// Renames variables (wherever they are read or assigned) by `f`.
fn rename_stmts(body: &mut [Stmt], f: &dyn Fn(&str) -> Option<String>) {
    for s in body {
        match &mut s.kind {
            StmtKind::Assign { targets, value } => {
                targets.iter_mut().for_each(|t| rename_expr(t, f));
                rename_expr(value, f);
            }
            StmtKind::AugAssign { target, value, .. } => {
                rename_expr(target, f);
                rename_expr(value, f);
            }
            StmtKind::AnnAssign { target, value, .. } => {
                rename_expr(target, f);
                if let Some(v) = value {
                    rename_expr(v, f);
                }
            }
            StmtKind::Expr(e) | StmtKind::Assert(e) | StmtKind::WaitUntil(e) | StmtKind::WaitTicks(e) | StmtKind::Return(Some(e)) => {
                rename_expr(e, f)
            }
            StmtKind::If { cond, body, orelse } => {
                rename_expr(cond, f);
                rename_stmts(body, f);
                rename_stmts(orelse, f);
            }
            StmtKind::While { cond, body } => {
                rename_expr(cond, f);
                rename_stmts(body, f);
            }
            StmtKind::For { target, iter, body } => {
                rename_expr(target, f);
                rename_expr(iter, f);
                rename_stmts(body, f);
            }
            StmtKind::Block { body, .. } => rename_stmts(body, f),
            _ => {}
        }
    }
}

fn rename_expr(e: &mut Expr, f: &dyn Fn(&str) -> Option<String>) {
    match &mut e.kind {
        ExprKind::Name(n) => {
            if let Some(m) = f(n) {
                *n = m;
            }
        }
        ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Str(_) => {}
        ExprKind::Unary(_, a) | ExprKind::Not(a) | ExprKind::Attr(a, _) => rename_expr(a, f),
        ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
            rename_expr(a, f);
            rename_expr(b, f);
        }
        ExprKind::Compare(a, rest) => {
            rename_expr(a, f);
            rest.iter_mut().for_each(|(_, x)| rename_expr(x, f));
        }
        ExprKind::BoolOp(_, items) | ExprKind::Tuple(items) | ExprKind::List(items) => items.iter_mut().for_each(|x| rename_expr(x, f)),
        ExprKind::IfExp { cond, then, orelse } => {
            rename_expr(cond, f);
            rename_expr(then, f);
            rename_expr(orelse, f);
        }
        // The function itself is not a variable.
        ExprKind::Call { args, kwargs, .. } => {
            args.iter_mut().for_each(|x| rename_expr(x, f));
            kwargs.iter_mut().for_each(|(_, x)| rename_expr(x, f));
        }
        ExprKind::ListComp { elt, target, iter, conds } => {
            for x in [elt, target, iter] {
                rename_expr(x, f);
            }
            conds.iter_mut().for_each(|x| rename_expr(x, f));
        }
        ExprKind::Dict(items) => items.iter_mut().for_each(|(k, v)| {
            rename_expr(k, f);
            rename_expr(v, f);
        }),
        ExprKind::DictComp { key, value, target, iter, conds } => {
            for x in [key, value, target, iter] {
                rename_expr(x, f);
            }
            conds.iter_mut().for_each(|x| rename_expr(x, f));
        }
    }
}

/// Names assigned on every path through straight-line code (for definite-assignment checks).
fn must_assign(body: &[Stmt], out: &mut BTreeSet<String>) {
    fn target(e: &Expr, out: &mut BTreeSet<String>) {
        match &e.kind {
            ExprKind::Name(n) => {
                out.insert(n.clone());
            }
            ExprKind::Tuple(items) => items.iter().for_each(|i| target(i, out)),
            _ => {}
        }
    }
    for s in body {
        match &s.kind {
            StmtKind::Assign { targets, .. } => targets.iter().for_each(|t| target(t, out)),
            StmtKind::AugAssign { target: t, .. } | StmtKind::AnnAssign { target: t, .. } => target(t, out),
            StmtKind::If { body, orelse, .. } => {
                let (mut a, mut b) = (BTreeSet::new(), BTreeSet::new());
                must_assign(body, &mut a);
                must_assign(orelse, &mut b);
                out.extend(a.intersection(&b).cloned());
            }
            _ => {}
        }
    }
}

fn parse_type(e: &Expr) -> Result<Ty, Diag> {
    match &e.kind {
        ExprKind::Name(n) if n == "int" => Ok(Ty::Int),
        ExprKind::Name(n) if n == "bool" => Ok(Ty::Bool),
        ExprKind::Name(n) if n == "Bundle" => Ok(Ty::Bundle),
        ExprKind::Name(n) if n == "Signal" => Ok(Ty::Signal),
        _ => Err(Diag::error(e.span, "expected a type: `int`, `bool`, `Bundle` or `Signal`")),
    }
}

/// Whether an expression is (syntactically) a bundle, given the names known to be bundles.
fn is_bundle_expr(e: &Expr, bundles: &HashSet<String>) -> bool {
    match &e.kind {
        ExprKind::Dict(_) | ExprKind::DictComp { .. } => true,
        ExprKind::Name(n) => bundles.contains(n),
        ExprKind::Call { func, .. } => matches!(&func.kind, ExprKind::Name(n)
            if matches!(n.as_str(), "Bundle" | "#bset" | "#arr" | "#vec" | "#amap" | "#aset" | "#aadd" | "#azeros" | "#asorted" | "#aidx" | "#rank" | "#drawb") || crate::stdlib::returns_bundle(n)),
        ExprKind::Binary(_, a, b) => is_bundle_expr(a, bundles) || is_bundle_expr(b, bundles),
        ExprKind::Unary(_, a) => is_bundle_expr(a, bundles),
        ExprKind::IfExp { then, orelse, .. } => is_bundle_expr(then, bundles) || is_bundle_expr(orelse, bundles),
        ExprKind::BoolOp(_, items) => items.iter().any(|i| is_bundle_expr(i, bundles)),
        _ => false,
    }
}

/// Names assigned something that isn't syntactically a bool somewhere.
fn nonbool_names(body: &[Stmt], out: &mut HashSet<String>) {
    for s in body {
        match &s.kind {
            StmtKind::Assign { targets, value } => {
                for t in targets {
                    match (&t.kind, &value.kind) {
                        (ExprKind::Name(n), _) if !is_bool_expr(value) => {
                            out.insert(n.clone());
                        }
                        (ExprKind::Tuple(ts), ExprKind::Tuple(vs)) if ts.len() == vs.len() => {
                            for (t, v) in ts.iter().zip(vs) {
                                if let (ExprKind::Name(n), false) = (&t.kind, is_bool_expr(v)) {
                                    out.insert(n.clone());
                                }
                            }
                        }
                        (ExprKind::Tuple(ts), _) => {
                            for t in ts {
                                if let ExprKind::Name(n) = &t.kind {
                                    out.insert(n.clone());
                                }
                            }
                        }
                        _ => {}
                    }
                }
            }
            StmtKind::AugAssign { target: Expr { kind: ExprKind::Name(n), .. }, .. } => {
                out.insert(n.clone());
            }
            StmtKind::If { body, orelse, .. } => {
                nonbool_names(body, out);
                nonbool_names(orelse, out);
            }
            StmtKind::While { body, .. } | StmtKind::For { body, .. } | StmtKind::Block { body, .. } | StmtKind::Sub { body, .. } => {
                nonbool_names(body, out)
            }
            _ => {}
        }
    }
}

/// Names that hold bundles: assigned a bundle anywhere (to a fixpoint, through copies).
fn bundle_names(bodies: &[&[Stmt]], mut known: HashSet<String>) -> HashSet<String> {
    fn scan(body: &[Stmt], known: &mut HashSet<String>) -> bool {
        fn mark(t: &Expr, v: &Expr, known: &mut HashSet<String>) -> bool {
            match (&t.kind, is_bundle_expr(v, known)) {
                (ExprKind::Name(n), true) => known.insert(n.clone()),
                _ => false,
            }
        }
        let mut changed = false;
        for s in body {
            match &s.kind {
                StmtKind::Assign { targets, value } => {
                    for t in targets {
                        match (&t.kind, &value.kind) {
                            (ExprKind::Tuple(ts), ExprKind::Tuple(vs)) if ts.len() == vs.len() => {
                                for (t, v) in ts.iter().zip(vs) {
                                    changed |= mark(t, v, known);
                                }
                            }
                            _ => changed |= mark(t, value, known),
                        }
                    }
                }
                StmtKind::AugAssign { target, value, .. } => changed |= mark(target, value, known),
                StmtKind::AnnAssign { target, ann, value } => {
                    if matches!(&ann.kind, ExprKind::Name(n) if n == "Bundle") {
                        if let ExprKind::Name(n) = &target.kind {
                            changed |= known.insert(n.clone());
                        }
                    } else if let Some(v) = value {
                        changed |= mark(target, v, known);
                    }
                }
                StmtKind::If { body, orelse, .. } => {
                    changed |= scan(body, known);
                    changed |= scan(orelse, known);
                }
                StmtKind::While { body, .. } | StmtKind::For { body, .. } | StmtKind::Block { body, .. } | StmtKind::Every { body, .. } => {
                    changed |= scan(body, known)
                }
                StmtKind::Sub { body, .. } => changed |= scan(body, known),
                _ => {}
            }
        }
        changed
    }
    loop {
        let mut changed = false;
        for b in bodies {
            changed |= scan(b, &mut known);
        }
        if !changed {
            return known;
        }
    }
}

/// Whether an expression is (syntactically) a runtime-capable signal, given the names known
/// to hold signals: `S(...)`, `.argmax()`/`.argmin()`, a loop's signal (`#hot`), a signal name,
/// or a choice between those.
fn is_signal_expr(e: &Expr, sigs: &HashSet<String>) -> bool {
    match &e.kind {
        ExprKind::Name(n) => sigs.contains(n),
        ExprKind::Call { func, args, .. } => match &func.kind {
            ExprKind::Name(n) => n == "S" || n == "#hot" || crate::stdlib::returns_signal(n),
            ExprKind::Attr(_, m) => args.is_empty() && (m == "argmax" || m == "argmin"),
            _ => false,
        },
        ExprKind::IfExp { then, orelse, .. } => is_signal_expr(then, sigs) || is_signal_expr(orelse, sigs),
        _ => false,
    }
}

/// Names that hold signals (to a fixpoint, through copies).
fn signal_names(bodies: &[&[Stmt]], mut known: HashSet<String>) -> HashSet<String> {
    fn scan(body: &[Stmt], known: &mut HashSet<String>) -> bool {
        fn mark(t: &Expr, v: &Expr, known: &mut HashSet<String>) -> bool {
            match (&t.kind, is_signal_expr(v, known)) {
                (ExprKind::Name(n), true) => known.insert(n.clone()),
                _ => false,
            }
        }
        let mut changed = false;
        for s in body {
            match &s.kind {
                StmtKind::Assign { targets, value } => {
                    for t in targets {
                        match (&t.kind, &value.kind) {
                            (ExprKind::Tuple(ts), ExprKind::Tuple(vs)) if ts.len() == vs.len() => {
                                for (t, v) in ts.iter().zip(vs) {
                                    changed |= mark(t, v, known);
                                }
                            }
                            _ => changed |= mark(t, value, known),
                        }
                    }
                }
                StmtKind::AnnAssign { target, ann, value } => {
                    if matches!(&ann.kind, ExprKind::Name(n) if n == "Signal") {
                        if let ExprKind::Name(n) = &target.kind {
                            changed |= known.insert(n.clone());
                        }
                    } else if let Some(v) = value {
                        changed |= mark(target, v, known);
                    }
                }
                StmtKind::If { body, orelse, .. } => {
                    changed |= scan(body, known);
                    changed |= scan(orelse, known);
                }
                StmtKind::While { body, .. } | StmtKind::For { body, .. } | StmtKind::Block { body, .. } | StmtKind::Every { body, .. } | StmtKind::Sub { body, .. } => {
                    changed |= scan(body, known)
                }
                _ => {}
            }
        }
        changed
    }
    loop {
        let mut changed = false;
        for b in bodies {
            changed |= scan(b, &mut known);
        }
        if !changed {
            return known;
        }
    }
}

/// Whether an expression is syntactically boolean (decides the type of un-annotated state).
fn is_bool_expr(e: &Expr) -> bool {
    match &e.kind {
        ExprKind::Bool(_) | ExprKind::Compare(..) | ExprKind::Not(_) => true,
        ExprKind::BoolOp(_, items) => items.iter().all(is_bool_expr),
        ExprKind::IfExp { then, orelse, .. } => is_bool_expr(then) && is_bool_expr(orelse),
        ExprKind::Call { func, .. } => matches!(&func.kind, ExprKind::Name(n) if n == "bool"),
        _ => false,
    }
}

/// Names for constant expressions: only previously defined constants.
struct ConstNames<'a> {
    consts: &'a HashMap<String, Cv>,
    ports: &'a [Port],
}

impl Names for ConstNames<'_> {
    fn lookup(&mut self, g: &mut Graph, name: &str, span: Span) -> Result<V, Diag> {
        if let Some(k) = self.consts.get(name) {
            return Ok(g.cv(k));
        }
        if self.ports.iter().any(|p| p.name == name) {
            return Err(Diag::error(span, format!("`{name}` is a port, so its value isn't known when compiling")));
        }
        Err(Diag::error(span, format!("`{name}` is not a constant")))
    }
}

/// The constant value of an expression (a number, bundle or signal).
pub fn eval_const(e: &Expr, consts: &HashMap<String, Cv>, ports: &[Port]) -> Result<Cv, Diag> {
    let mut g = Graph::default();
    let v = lower::expr(&mut g, &mut ConstNames { consts, ports }, e)?;
    // With `--checks`, a failing check (division by zero) leaves it to run time.
    if let Some((_, span, what)) = g.checks.first() {
        return Err(Diag::error(*span, format!("{what} in a constant expression")));
    }
    g.as_cv(v).ok_or_else(|| Diag::error(e.span, "expected a constant expression"))
}

/// A constant integer expression.
pub fn eval_int(e: &Expr, consts: &HashMap<String, Cv>, ports: &[Port]) -> Result<i32, Diag> {
    eval_const(e, consts, ports)?.int().ok_or_else(|| Diag::error(e.span, "expected a number"))
}

fn parse_port(table: &SignalTable, s: &Stmt, consts: &HashMap<String, Cv>) -> Result<Port, Diag> {
    let StmtKind::Port { dir, name, ty, signal, label } = &s.kind else { unreachable!() };
    let ty = parse_type(ty)?;
    if ty.is_bun() {
        if let Some((_, sp)) = signal {
            let what = if ty == Ty::Bundle { "a bundle port carries every signal" } else { "a `Signal` port carries a signal (with value 1)" };
            return Err(Diag::error(*sp, format!("{what}, so it has no `@ signal`")));
        }
    }
    let sig = match signal {
        _ if ty.is_bun() => table.special("signal-each"),
        Some((SignalSpec::Ident(n), sp)) => crate::bundle::ident(n, *sp),
        Some((SignalSpec::Exact(n), sp)) => crate::bundle::exact(n, None, *sp),
        Some((SignalSpec::Expr(e), sp)) => match eval_const(e, consts, &[])? {
            Cv::Sig(s) => s,
            _ => return Err(Diag::error(*sp, "expected a signal after `@`, e.g. S(\"nt-fuel\", type=\"recipe\")")),
        },
        None => {
            // Default: the name's first letter, e.g. `total` → signal-T.
            let letter = name.chars().find(|c| c.is_ascii_alphabetic()).unwrap_or('A').to_ascii_uppercase();
            table.resolve_ident(&letter.to_string()).unwrap()
        }
    };
    let label = match label {
        None => None,
        Some(Expr { kind: ExprKind::Call { func, args, .. }, .. })
            if matches!(&func.kind, ExprKind::Name(n) if n == "port")
                && matches!(args.first().map(|a| &a.kind), Some(ExprKind::Str(_))) =>
        {
            let ExprKind::Str(text) = &args[0].kind else { unreachable!() };
            Some(text.clone())
        }
        Some(e) => return Err(Diag::error(e.span, "expected `port(\"label\")`")),
    };
    Ok(Port { name: name.clone(), dir: *dir, ty, sig, label, span: s.span })
}

/// With `TICKY_TIMING` set, prints how long each compiler phase takes.
pub fn timing(what: &str, since: crate::clock::Instant) {
    if std::env::var_os("TICKY_TIMING").is_some() {
        eprintln!("[timing] {what}: {:.1} ms", since.elapsed().as_secs_f64() * 1000.0);
    }
}

pub fn analyze(m: &Module, pipeline: bool) -> Result<Program, Vec<Diag>> {
    analyze_with_pipelines(m, pipeline, &[])
}

/// Optional per-block choices; omitted entries use `pipeline`.
pub(crate) fn analyze_with_pipelines(m: &Module, pipeline: bool, choices: &[bool]) -> Result<Program, Vec<Diag>> {
    let t = crate::clock::Instant::now();
    let mut m = m.clone();
    crate::strconst::substitute(&mut m)?;
    let imported = crate::stdlib::imports(&m)?;
    crate::stdlib::rewrite_calls(&mut m, &imported)?;
    let controls = crate::stdlib::controls(&mut m, &imported)?;
    let random = if imported.contains("random") { crate::stdlib::random_names(&m) } else { Default::default() };
    let (m, screens) = crate::display::desugar(&m)?;
    let mem: std::collections::HashSet<String> = screens.iter().map(|s| s.var.clone()).collect();
    let (expanded, (calls, subs)) = crate::expand::expand_module(&m, &mem)?;
    timing("expand", t);
    let mut p = crate::modsched::choose(|| analyze_expanded(&expanded, pipeline, choices, &mem))?;
    p.screens = screens;
    p.random = random;
    p.controls = controls;
    timing("analyze", t);
    p.calls = calls;
    p.subroutines = subs;
    Ok(p)
}

/// `peripherals`: variables shown by screens, readouts, panels and speakers.
fn analyze_expanded(m: &Module, pipeline: bool, choices: &[bool], peripherals: &HashSet<String>) -> Result<Program, Vec<Diag>> {
    let t0 = crate::clock::Instant::now();
    let table = SignalTable::base();
    let mut errs = Vec::new();
    let mut ports: Vec<Port> = Vec::new();
    let mut every: Vec<(&Stmt, Option<&Expr>, &[Stmt])> = Vec::new();
    let mut tests = Vec::new();
    let mut top: Vec<&Stmt> = Vec::new();
    let mut subs: Vec<cfg::SubDef> = Vec::new();
    let mut procs_src: Vec<(String, Vec<Stmt>)> = Vec::new();

    for s in &m.body {
        match &s.kind {
            StmtKind::Port { name, .. } => {
                if ports.iter().any(|p| &p.name == name) {
                    errs.push(Diag::error(s.span, format!("port `{name}` is declared twice")));
                    continue;
                }
                match parse_port(table, s, &HashMap::new()) {
                    Ok(p) => ports.push(p),
                    Err(d) => errs.push(d),
                }
            }
            StmtKind::Every { period, body } => every.push((s, period.as_ref(), body)),
            StmtKind::Test { name, body } => tests.push(TestDef { name: name.clone(), span: s.span, body: body.clone() }),
            StmtKind::Process { name, body } => procs_src.push((name.clone(), body.clone())),
            StmtKind::Expr(Expr { kind: ExprKind::Str(_), .. }) => {} // docstring
            StmtKind::Sub { name, label, body } => subs.push((name.clone(), *label, body.clone())),
            _ => top.push(s),
        }
    }

    // `--checks`: a dedicated output for the error code.
    let error_port = if crate::checks_on() {
        if let Some(p) = ports.iter().find(|p| p.name == "error") {
            errs.push(Diag::error(p.span, "with `--checks`, the port name `error` is reserved for the error code"));
        }
        let table = SignalTable::base();
        ports.push(Port {
            name: "error".into(),
            dir: PortDir::Output,
            ty: Ty::Int,
            sig: table.lookup("signal-E").unwrap(),
            label: Some("error code (--checks)".into()),
            span: Span::default(),
        });
        Some(ports.len() - 1)
    } else {
        None
    };

    // Prologue: the leading top-level statements that can run entirely at compile time (no
    // ports, no waits) are executed now; the names they assign become constants, or initial
    // values if something assigns them again later.
    let mut pro: HashMap<String, Cv> = HashMap::new();
    let mut pro_exprs: HashMap<String, (Option<Expr>, Expr, Span)> = HashMap::new();
    let mut split = 0;
    for s in &top {
        let mut env = pro.clone();
        let mut exprs = pro_exprs.clone();
        let mut budget = 1_000_000usize;
        match crate::consteval::exec(std::slice::from_ref(*s), &subs, &mut env, &mut exprs, &ports, &mut budget) {
            Ok(()) => {
                pro = env;
                pro_exprs = exprs;
                split += 1;
            }
            Err(_) => break,
        }
    }
    let mut pro_order: Vec<(String, Option<&Expr>, &Expr, Span)> = Vec::new();
    for (n, (ann, value, span)) in &pro_exprs {
        pro_order.push((n.clone(), ann.as_ref(), value, *span));
    }
    pro_order.sort_by_key(|p| p.3.start);
    let pending: Vec<Stmt> = top[split..].iter().map(|s| (*s).clone()).collect();
    timing("prologue", t0);
    let main_stmts: Vec<Stmt> = pending.into_iter().collect();

    // A process's variables are its own (renamed `P:x`), except those with an initial value
    // at the top of the file and ports: only those can be shared (anything else can't be read
    // by another process, which might not have assigned it yet).
    for (pname, body) in &mut procs_src {
        let ns = format!("{pname}:");
        let mut names = BTreeMap::new();
        let mut ignore = Vec::new();
        assigned_names(body, &mut names, &mut ignore);
        for (_, _, b) in subs.iter().filter(|(n, _, _)| n.starts_with(&ns)) {
            assigned_names(b, &mut names, &mut ignore);
        }
        let own: HashSet<String> =
            names.into_keys().filter(|n| !pro.contains_key(n) && !ports.iter().any(|p| &p.name == n) && !n.starts_with(&ns)).collect();
        let f = |n: &str| own.contains(n).then(|| format!("{ns}{n}"));
        rename_stmts(body, &f);
        for (n, _, b) in subs.iter_mut() {
            if n.starts_with(&ns) {
                rename_stmts(b, &f);
            }
        }
    }

    // Who assigns what.
    let mut block_assigns: Vec<BTreeMap<String, Span>> = Vec::new();
    for (_, _, body) in &every {
        let mut names = BTreeMap::new();
        assigned_names(body, &mut names, &mut errs);
        block_assigns.push(names);
    }
    // Subroutines belong to the process that calls them (`P:f` in process `P`).
    let subs_of = |proc: Option<&str>| -> Vec<cfg::SubDef> {
        subs.iter().filter(|(n, _, _)| n.split_once(':').map(|(p, _)| p) == proc).cloned().collect()
    };
    let mut main_assigns = BTreeMap::new();
    assigned_names(&main_stmts, &mut main_assigns, &mut errs);
    for (_, _, body) in &subs_of(None) {
        assigned_names(body, &mut main_assigns, &mut errs);
    }
    let mut proc_assigns: Vec<BTreeMap<String, Span>> = Vec::new();
    for (name, body) in &procs_src {
        let mut names = BTreeMap::new();
        assigned_names(body, &mut names, &mut errs);
        for (_, _, b) in &subs_of(Some(name)) {
            assigned_names(b, &mut names, &mut errs);
        }
        proc_assigns.push(names);
    }

    let mut consts: HashMap<String, Cv> = HashMap::new();
    for (n, _, _, span) in &pro_order {
        if let Some(p) = ports.iter().find(|p| &p.name == n) {
            if p.dir == PortDir::Input {
                errs.push(Diag::error(*span, format!("`{n}` is an input; inputs can't be assigned")));
            }
            continue;
        }
        if !main_assigns.contains_key(n) && !block_assigns.iter().any(|b| b.contains_key(n)) && !proc_assigns.iter().any(|b| b.contains_key(n)) {
            consts.insert(n.clone(), pro[n].clone());
        }
    }

    let konst = |e: &Expr| eval_int(e, &consts, &ports).ok();
    // Names each piece of code mentions (main, each process, with their subroutines; the
    // `every` blocks): what a process's steps write early under profile-guided speculation
    // must be invisible to the rest and to the ports.
    let mut unit_names: Vec<BTreeSet<String>> = Vec::new();
    for proc in std::iter::once(None).chain(procs_src.iter().map(|(n, _)| Some(n.as_str()))) {
        let mut m = BTreeSet::new();
        crate::liveness::mentioned(proc.map_or(&main_stmts[..], |n| &procs_src.iter().find(|(p, _)| p == n).unwrap().1[..]), &mut m);
        subs_of(proc).iter().for_each(|(_, _, b)| crate::liveness::mentioned(b, &mut m));
        unit_names.push(m);
    }
    {
        let mut m = BTreeSet::new();
        every.iter().for_each(|(_, _, b)| crate::liveness::mentioned(b, &mut m));
        unit_names.push(m);
    }
    let observable = |unit: usize| {
        let unit_names = &unit_names;
        let ports = &ports;
        move |n: &str| peripherals.contains(n) || ports.iter().any(|p| p.name == n) || unit_names.iter().enumerate().any(|(k, m)| k != unit && m.contains(n))
    };
    let main_cfg = if main_stmts.is_empty() {
        None
    } else {
        match cfg::build("main", &main_stmts, &subs_of(None), &konst, &observable(0)) {
            Ok(c) => {
                for h in &c.hidden {
                    main_assigns.insert(h.clone(), main_stmts[0].span);
                }
                Some(c)
            }
            Err(d) => {
                errs.push(d);
                None
            }
        }
    };
    let mut proc_cfgs = Vec::new();
    for (k, (name, body)) in procs_src.iter().enumerate() {
        let span = body.first().map(|s| s.span).unwrap_or_default();
        match cfg::build(name, body, &subs_of(Some(name)), &konst, &observable(k + 1)) {
            Ok(c) => {
                for h in &c.hidden {
                    proc_assigns[k].insert(h.clone(), span);
                }
                proc_cfgs.push(Some(c));
            }
            Err(d) => {
                errs.push(d);
                proc_cfgs.push(None);
            }
        }
    }

    // Which names hold bundles.
    let mut seed: HashSet<String> = ports.iter().filter(|p| p.ty == Ty::Bundle).map(|p| p.name.clone()).collect();
    seed.extend(pro.iter().filter(|(_, v)| matches!(v, Cv::Bun(_))).map(|(n, _)| n.clone()));
    let mut bodies: Vec<&[Stmt]> = vec![&main_stmts];
    bodies.extend(every.iter().map(|(_, _, b)| *b));
    bodies.extend(procs_src.iter().map(|(_, b)| b.as_slice()));
    bodies.extend(subs.iter().map(|(_, _, b)| b.as_slice()));
    let bundles = bundle_names(&bodies, seed);
    let sig_seed: HashSet<String> = ports.iter().filter(|p| p.ty == Ty::Signal).map(|p| p.name.clone()).collect();
    let signals = signal_names(&bodies, sig_seed);
    let mut nonbool = HashSet::new();
    for b in &bodies {
        nonbool_names(b, &mut nonbool);
    }

    // States: anything assigned by a process, plus outputs.
    let mut states: Vec<State> = Vec::new();
    let mut names: Vec<String> = main_assigns.keys().cloned().collect();
    for b in &proc_assigns {
        names.extend(b.keys().cloned());
    }
    for b in &block_assigns {
        for n in b.keys() {
            // Names assigned only inside one block with no prologue value are block temporaries.
            let is_port = ports.iter().any(|p| &p.name == n);
            if pro.contains_key(n) || is_port || main_assigns.contains_key(n) || proc_assigns.iter().any(|b| b.contains_key(n)) {
                names.push(n.clone());
            }
        }
    }
    for p in &ports {
        if p.dir == PortDir::Output {
            names.push(p.name.clone());
        }
    }
    let mut seen = HashSet::new();
    names.retain(|n| seen.insert(n.clone()));
    for n in names {
        if let Some(p) = ports.iter().find(|p| p.name == n && p.dir == PortDir::Input) {
            let span = main_assigns
                .get(&n)
                .or_else(|| block_assigns.iter().chain(&proc_assigns).find_map(|b| b.get(&n)))
                .copied()
                .unwrap_or(p.span);
            errs.push(Diag::error(span, format!("`{n}` is an input; inputs can't be assigned")));
            continue;
        }
        let mut writers: Vec<(usize, Span)> = Vec::new();
        if let Some(sp) = main_assigns.get(&n) {
            writers.push((MAIN, *sp));
        }
        for (k, b) in proc_assigns.iter().enumerate() {
            if let Some(sp) = b.get(&n) {
                writers.push((proc_owner(k), *sp));
            }
        }
        for (bi, b) in block_assigns.iter().enumerate() {
            if let Some(sp) = b.get(&n) {
                writers.push((bi, *sp));
            }
        }
        if writers.len() > 1 {
            errs.push(Diag::error(writers[1].1, format!("{} is assigned by more than one process", crate::expand::quoted(&n)))
                .with_help("each variable may only be written by one process or `every` block (the single-writer rule); give each its own variable and combine them in the reader"));
        }
        let port = ports.iter().position(|p| p.name == n);
        let pro_entry = pro_order.iter().find(|(name, ..)| *name == n);
        let ty = match (port, pro_entry) {
            (Some(pi), _) => ports[pi].ty,
            (None, Some((_, Some(ann), _, _))) => match parse_type(ann) {
                Ok(t) => t,
                Err(d) => {
                    errs.push(d);
                    Ty::Int
                }
            },
            _ if bundles.contains(&n) => Ty::Bundle,
            _ if signals.contains(&n) => Ty::Signal,
            // A bool only if every assignment is one (`a = x > 0` once doesn't make `a = 5` an error).
            (None, Some((_, None, value, _))) if is_bool_expr(value) && !nonbool.contains(&n) => Ty::Bool,
            _ => Ty::Int,
        };
        let span = pro_entry.map(|p| p.3).or(writers.first().map(|w| w.1)).unwrap_or_default();
        let (mut init, mut binit) = (0, Vec::new());
        match (pro.get(&n), ty) {
            (None, _) => {}
            (Some(Cv::Int(k)), Ty::Int | Ty::Bool) => init = *k,
            (Some(Cv::Bun(b)), Ty::Bundle) => binit = b.clone(),
            (Some(Cv::Sig(sg)), Ty::Signal) => binit = vec![(*sg, 1)],
            (Some(_), _) => errs.push(Diag::error(span, format!("{} is a {}, but its initial value isn't", crate::expand::quoted(&n), ty.name()))),
        }
        if ty == Ty::Bool && !(0..=1).contains(&init) {
            errs.push(Diag::error(span, format!("`{n}` is a bool, but its initial value is {init}")));
        }
        states.push(State {
            has_init: pro.contains_key(&n) || port.is_some(),
            name: n,
            ty,
            init,
            binit,
            owner: writers.first().map(|w| w.0),
            port,
            span,
            shared: Vec::new(),
        });
    }
    if !errs.is_empty() {
        return Err(errs);
    }

    let mut blocks = Vec::new();
    let mut warnings = Vec::new();
    for (bi, (stmt, period, body)) in every.iter().enumerate() {
        let pipeline = choices.get(bi).copied().unwrap_or(pipeline);
        // Readouts' drawing blocks (`display::NATURAL`): as often as they can, unpipelined.
        let natural = matches!(period, Some(Expr { kind: ExprKind::Name(n), .. }) if n == crate::display::NATURAL);
        let requested = match period {
            None => None,
            Some(_) if natural => None,
            Some(e) => match eval_int(e, &consts, &ports) {
                Ok(n) if n >= 1 => Some(n as u32),
                Ok(n) => {
                    errs.push(Diag::error(e.span, format!("the period must be at least 1 tick, not {n}")));
                    continue;
                }
                Err(d) => {
                    errs.push(d);
                    continue;
                }
            },
        };
        let ctx = Ctx { owner: bi, ports: &ports, states: &states, consts: &consts };
        match lower_block(&ctx, body) {
            Ok((srcs, mut graph, mut next)) => {
                let mut plans = Vec::new();
                let mut raw = std::mem::take(&mut graph.checks);
                {
                    let roots: Vec<V> = next.iter().map(|(_, v)| *v).chain(raw.iter().map(|c| c.0)).collect();
                    let no_const: Vec<bool> = next.iter().map(|_| false).chain(raw.iter().map(|_| true)).collect();
                    if let Some(new) = crate::egraph::optimize(&mut graph, &roots, &no_const, &format!("every block {bi}")) {
                        let (w, c) = new.split_at(next.len());
                        next.iter_mut().zip(w).for_each(|(x, v)| x.1 = *v);
                        raw.iter_mut().zip(c).for_each(|(x, v)| x.0 = *v);
                    }
                }
                let mut fz = Fuser::new(&mut graph);
                let roots: Vec<V> = next.iter().map(|(_, v)| *v).chain(raw.iter().map(|c| c.0)).collect();
                fz.plan_order_stats(&roots, pipeline && requested.is_none() && raw.is_empty() && !natural);
                let mut tv = crate::ir_export::Writer { name: "iteration".into(), writes: next.clone(), ..Default::default() };
                for (si, v) in next {
                    let own = srcs.iter().position(|k| *k == SrcKind::Own(si)).map(|id| fz.g.src(id as u32));
                    if let Some(p) = fz.writer_plan(v, own) {
                        plans.push((si, p));
                    }
                }
                if crate::ir_export::on() {
                    tv.checks = raw.iter().map(|c| (c.0, fz.rebuild(c.0))).collect(); // memoised: fused_checks gets the same
                }
                let checks = fused_checks(&mut fz, raw);
                // A block with runtime checks runs multi-cycle, so a check is read on the
                // commit pulse with the rest of its iteration.
                let pipe = if pipeline && requested.is_none() && checks.is_empty() && !natural {
                    crate::pipeline::plan(&mut graph, &srcs, &mut plans)
                } else {
                    None
                };
                let depths = graph.depths();
                let depth = plans.iter().map(|(_, p)| p.ready(&depths)).chain(checks.iter().map(|c| depths[c.fail as usize] + 1)).max().unwrap_or(0);
                let needed = if pipe.is_some() { 1 } else { depth + 1 };
                let header = Span::new(stmt.span.start, stmt.span.start + 5);
                let period = match requested {
                    Some(n) if n < needed => {
                        errs.push(Diag::error(header, format!(
                            "this block needs at least {needed} ticks per iteration, but asks for {n}"
                        )).with_help(format!("its longest calculation is {depth} combinators deep; use `every {needed} ticks:` or simplify it")));
                        continue;
                    }
                    Some(n) => n,
                    None => {
                        if needed > 1 && !natural {
                            warnings.push(Diag::warning(header, format!(
                                "this block can only run every {needed} ticks, not every tick"
                            )).with_help(format!(
                                "a value feeds back into itself through {depth} combinators; write `every {needed} ticks:` to make the rate explicit"
                            )));
                        }
                        needed
                    }
                };
                if crate::ir_export::on() {
                    tv.plans = plans.clone();
                    tv.accs = pipe.as_ref().map(|p| p.accs.clone()).unwrap_or_default();
                    crate::ir_export::unit(&format!("every block {bi}"), &graph, &srcs, &states, &ports, &[tv]);
                }
                blocks.push(Block { span: stmt.span, checks, requested, srcs, graph, plans, depth, period, pipe });
            }
            Err(d) => errs.push(d),
        }
    }

    timing("blocks", t0);
    let mut procs = Vec::new();
    let all = std::iter::once((MAIN, "main".to_string(), main_cfg))
        .chain(proc_cfgs.into_iter().enumerate().map(|(k, c)| (proc_owner(k), procs_src[k].0.clone(), c)));
    // Names each process's code mentions (its own body and subroutines), for register
    // sharing: a variable mentioned by any other code is never shared.
    let mut code: Vec<(Option<usize>, BTreeSet<String>)> = Vec::new();
    {
        let mut m = BTreeSet::new();
        crate::liveness::mentioned(&main_stmts, &mut m);
        subs_of(None).iter().for_each(|(_, _, b)| crate::liveness::mentioned(b, &mut m));
        code.push((Some(MAIN), m));
        for (k, (name, body)) in procs_src.iter().enumerate() {
            let mut m = BTreeSet::new();
            crate::liveness::mentioned(body, &mut m);
            subs_of(Some(name)).iter().for_each(|(_, _, b)| crate::liveness::mentioned(b, &mut m));
            code.push((Some(proc_owner(k)), m));
        }
        let mut m = BTreeSet::new();
        every.iter().for_each(|(_, _, b)| crate::liveness::mentioned(b, &mut m));
        code.push((None, m));
    }
    let mut merged = BTreeMap::new();
    for (owner, name, c) in all {
        let Some(mut c) = c else { continue };
        let elsewhere: BTreeSet<&String> = code.iter().filter(|(o, _)| *o != Some(owner)).flat_map(|(_, m)| m).collect();
        merged.extend(share_registers(&mut c, owner, &states, &elsewhere));
        let ctx = Ctx { owner, ports: &ports, states: &states, consts: &consts };
        match lower_main(&ctx, &c, &elsewhere) {
            Ok(mut m) => {
                m.name = name;
                m.owner = owner;
                procs.push(m);
            }
            Err(d) => errs.push(d),
        }
    }
    if !errs.is_empty() {
        return Err(errs);
    }
    // A shared register's descriptions name every variable in it.
    for (member, rep) in merged {
        if let Some(s) = states.iter_mut().find(|s| s.name == rep) {
            s.shared.push(member);
        }
    }
    // Error codes, in order: `every` blocks, then each process's steps.
    let mut sites = Vec::new();
    for b in &mut blocks {
        for c in &mut b.checks {
            sites.push(CheckSite { span: c.span, what: c.what, owner: "every".into() });
            c.code = sites.len() as i32;
        }
    }
    for m in &mut procs {
        for st in &mut m.steps {
            for c in &mut st.checks {
                sites.push(CheckSite { span: c.span, what: c.what, owner: m.name.clone() });
                c.code = sites.len() as i32;
            }
        }
    }
    warnings.extend(crate::bundle::take_warnings());
    Ok(Program { calls: Default::default(), subroutines: Default::default(), ports, states, consts, blocks, procs, tests, warnings, screens: Vec::new(), random: Default::default(), controls: Vec::new(), checks: sites, error_port })
}

/// What a process can see.
struct Ctx<'a> {
    owner: usize,
    ports: &'a [Port],
    states: &'a [State],
    consts: &'a HashMap<String, Cv>,
}

#[derive(Clone)]
enum Binding {
    Val(V),
    /// Assigned on some paths only.
    Maybe(Span),
}

struct ProcNames<'a> {
    ctx: &'a Ctx<'a>,
    env: BTreeMap<String, Binding>,
    srcs: Vec<SrcKind>,
    /// Interval assumed for each own state (by state index).
    own_iv: &'a HashMap<usize, Iv>,
    /// Read inputs and other processes' state unsampled (for `wait until`).
    live: bool,
    /// Main-process variables without an initial value that are definitely assigned here.
    defined: Option<&'a BTreeSet<String>>,
}

impl ProcNames<'_> {
    fn src_for(&mut self, g: &mut Graph, kind: SrcKind) -> V {
        let id = match self.srcs.iter().position(|k| *k == kind) {
            Some(i) => i as SrcId,
            None => {
                let states = self.ctx.states;
                let bun = match kind {
                    SrcKind::Own(s) | SrcKind::Foreign(s) | SrcKind::LiveForeign(s) => states[s].ty.is_bun(),
                    SrcKind::Input(p) | SrcKind::LiveInput(p) => self.ctx.ports[p].ty.is_bun(),
                    SrcKind::Ticks | SrcKind::LiveTicks => false,
                };
                // Signal state is a one-hot bundle; a Signal input is normalised when read.
                let sig = matches!(kind, SrcKind::Own(s) | SrcKind::Foreign(s) | SrcKind::LiveForeign(s) if states[s].ty == Ty::Signal);
                let iv = match kind {
                    // A bundle's interval is its elements' (see `initial_ivs`).
                    SrcKind::Own(s) if states[s].ty == Ty::Bundle => self.own_iv[&s],
                    _ if bun => Iv::FULL,
                    SrcKind::Own(s) => self.own_iv[&s],
                    SrcKind::Foreign(s) | SrcKind::LiveForeign(s) if states[s].ty == Ty::Bool => Iv::BOOL,
                    SrcKind::Ticks | SrcKind::LiveTicks => Iv { lo: 0, hi: i32::MAX as i64 },
                    _ => Iv::FULL,
                };
                self.srcs.push(kind);
                g.src_iv.push(iv);
                g.src_bun.push(bun);
                while g.src_sig.len() < g.src_bun.len() - 1 {
                    g.src_sig.push(false);
                }
                g.src_sig.push(sig);
                (self.srcs.len() - 1) as SrcId
            }
        };
        g.src(id)
    }
}

impl Names for ProcNames<'_> {
    fn lookup(&mut self, g: &mut Graph, name: &str, span: Span) -> Result<V, Diag> {
        match self.env.get(name) {
            Some(Binding::Val(v)) => return Ok(*v),
            Some(Binding::Maybe(_)) => {
                return Err(Diag::error(span, format!("{} might not be assigned yet here", crate::expand::quoted(name)))
                    .with_help("it's only assigned on some paths through the `if` above; assign it on every path, or give it an initial value at the top of the file"));
            }
            None => {}
        }
        if let Some(k) = self.ctx.consts.get(name) {
            return Ok(g.cv(k));
        }
        if let Some(si) = self.ctx.states.iter().position(|s| s.name == name) {
            let s = &self.ctx.states[si];
            let unassigned_main = s.owner.is_some_and(is_proc) && !s.has_init;
            if unassigned_main && s.owner != Some(self.ctx.owner) {
                let who = if s.owner == Some(MAIN) { "the main program" } else { "another process" };
                return Err(Diag::error(span, format!("{} is set by {who}, which might not have run yet", crate::expand::quoted(name)))
                    .with_help(format!("give it an initial value at the top of the file, e.g. `{name} = 0`")));
            }
            if unassigned_main && !self.defined.is_some_and(|d| d.contains(name)) {
                let plain = name.split_once(':').map_or(name, |(_, n)| n);
                return Err(Diag::error(span, format!("{} might be used before it's assigned", crate::expand::quoted(name)))
                    .with_help(format!("assign it first on every path, or give it an initial value at the top of the file, e.g. `{plain} = 0`")));
            }
            return Ok(match s.owner {
                Some(o) if o == self.ctx.owner => self.src_for(g, SrcKind::Own(si)),
                Some(_) if self.live => self.src_for(g, SrcKind::LiveForeign(si)),
                Some(_) => self.src_for(g, SrcKind::Foreign(si)),
                None if s.ty == Ty::Bundle => g.bconst(s.binit.iter().copied()),
                None if s.ty == Ty::Signal => {
                    let k = g.bconst(s.binit.iter().copied());
                    g.sigval(k)
                }
                None => g.konst(s.init),
            });
        }
        if let Some(s) = self.ctx.states.iter().find(|s| s.name.split_once(':').is_some_and(|(_, own)| own == name)) {
            let owner = s.name.split_once(':').map_or("", |(p, _)| p);
            return Err(Diag::error(span, format!("{} is not defined here: it belongs to process `{owner}`", crate::expand::quoted(name)))
                .with_help(format!("a variable a process assigns is its own unless the top level assigns it too; to share it, give it an initial value at the top of the file, e.g. `{name} = 0`")));
        }
        if let Some(pi) = self.ctx.ports.iter().position(|p| p.name == name) {
            let v = self.src_for(g, if self.live { SrcKind::LiveInput(pi) } else { SrcKind::Input(pi) });
            return Ok(match self.ctx.ports[pi].ty {
                Ty::Bool => g.truth(v),
                // A Signal input: the signal with the largest value on its wires.
                Ty::Signal => {
                    let top = g.brank(v, true, 0);
                    g.onehot(top)
                }
                _ => v,
            });
        }
        Err(Diag::error(span, format!("{} is not defined", crate::expand::quoted(name))))
    }

    fn ticks(&mut self, g: &mut Graph, _span: Span) -> Result<V, Diag> {
        Ok(self.src_for(g, if self.live { SrcKind::LiveTicks } else { SrcKind::Ticks }))
    }
}

fn exec(g: &mut Graph, n: &mut ProcNames, body: &[Stmt]) -> Result<(), Diag> {
    for s in body {
        match &s.kind {
            StmtKind::Pass => {}
            StmtKind::Assign { targets, value } => {
                let vals = rhs(g, n, value)?;
                for t in targets {
                    assign(g, n, t, &vals, value.span)?;
                }
            }
            StmtKind::AnnAssign { target, ann, value } => {
                let ty = parse_type(ann)?;
                let Some(value) = value else {
                    return Err(Diag::error(s.span, "a declaration needs a value here"));
                };
                let v = lower::expr(g, n, value)?;
                if ty == Ty::Bool && !g.is_bool(v) {
                    return Err(Diag::error(value.span, "expected a bool value"));
                }
                let k = crate::bundle::kind(g, v);
                let ok = match ty {
                    Ty::Bundle => k == crate::bundle::Kind::Bundle,
                    Ty::Signal => k.is_signal(),
                    Ty::Int | Ty::Bool => k == crate::bundle::Kind::Int,
                };
                if !ok {
                    return Err(Diag::error(value.span, format!("expected {}", match ty {
                        Ty::Bundle => "a bundle",
                        Ty::Signal => "a signal",
                        _ => "a number",
                    })));
                }
                assign(g, n, target, &[v], value.span)?;
            }
            StmtKind::AugAssign { target, op, value } => {
                let ExprKind::Name(name) = &target.kind else {
                    return Err(Diag::error(target.span, "can only assign to names here"));
                };
                if *op == ticky_syntax::ast::BinOp::Div {
                    return Err(Diag::error(s.span, "`/=` makes a float, and Ticky has no floats").with_help("use `//=`"));
                }
                let cur = n.lookup(g, name, target.span)?;
                let rhs = lower::expr(g, n, value)?;
                let v = if g.is_bundle(cur) || g.is_bundle(rhs) {
                    crate::bundle::binop(g, *op, cur, rhs, s.span)?
                } else {
                    let cur = crate::bundle::int(g, cur, target.span)?;
                    let rhs = crate::bundle::int(g, rhs, value.span)?;
                    if matches!(op, ticky_syntax::ast::BinOp::FloorDiv | ticky_syntax::ast::BinOp::Mod) {
                        lower::div_check(g, rhs, s.span);
                    }
                    lower::binop(g, *op, cur, rhs)
                };
                assign(g, n, target, &[v], s.span)?;
            }
            StmtKind::If { cond, body, orelse } => {
                let c = lower::expr(g, n, cond)?;
                let c = g.truth(c);
                let before = n.env.clone();
                g.path.push(c);
                let r = exec(g, n, body);
                g.path.pop();
                r?;
                let then_env = std::mem::replace(&mut n.env, before.clone());
                let nc = g.not(c);
                g.path.push(nc);
                let r = exec(g, n, orelse);
                g.path.pop();
                r?;
                let else_env = std::mem::take(&mut n.env);
                let mut merged = before.clone();
                let keys: BTreeSet<&String> = then_env.keys().chain(else_env.keys()).collect();
                for k in keys {
                    let side = |env: &BTreeMap<String, Binding>, g: &mut Graph, n: &mut ProcNames| -> Result<Binding, Diag> {
                        Ok(match env.get(k).or_else(|| before.get(k)) {
                            Some(b) => b.clone(),
                            // Unassigned on this side: the variable's current value, if it has one.
                            None if n.ctx.states.iter().any(|st| &st.name == k) => match n.lookup(g, k, s.span) {
                                Ok(v) => Binding::Val(v),
                                Err(_) => Binding::Maybe(s.span),
                            },
                            None => Binding::Maybe(s.span),
                        })
                    };
                    let (a, b) = (side(&then_env, g, n)?, side(&else_env, g, n)?);
                    let m = match (a, b) {
                        (Binding::Val(x), Binding::Val(y)) => {
                            let (kx, ky) = (crate::bundle::kind(g, x), crate::bundle::kind(g, y));
                            if kx != ky && !(kx.is_signal() && ky.is_signal()) {
                                return Err(Diag::error(s.span, format!("{} is a bundle on one side of this `if` but not the other", crate::expand::quoted(k))));
                            }
                            Binding::Val(g.mux(c, x, y))
                        }
                        (Binding::Maybe(sp), _) | (_, Binding::Maybe(sp)) => Binding::Maybe(sp),
                    };
                    merged.insert(k.clone(), m);
                }
                n.env = merged;
            }
            StmtKind::Expr(e) => {
                if !matches!(e.kind, ExprKind::Str(_)) {
                    lower::expr(g, n, e)?;
                    return Err(Diag::error(s.span, "this expression has no effect"));
                }
            }
            StmtKind::While { .. } | StmtKind::For { .. } => {
                return Err(Diag::error(s.span, "loops can't be used inside `every` blocks")
                    .with_help("`every` blocks already repeat; write loops in the main program instead"))
            }
            StmtKind::WaitUntil(_) | StmtKind::WaitTicks(_) => {
                return Err(Diag::error(s.span, "`wait` can't be used in an `every` block")
                    .with_help("`every` blocks run continuously; waiting belongs in the main program"))
            }
            // Only present with `--checks` (the expansion drops asserts otherwise).
            StmtKind::Assert(e) => {
                let what = match &e.kind {
                    ExprKind::Call { func, .. } if matches!(&func.kind, ExprKind::Name(f) if f == "#ixok") => "index out of range",
                    _ => "assertion failed",
                };
                let v = lower::expr(g, n, e)?;
                let ok = g.truth(v);
                let fail = g.not(ok);
                g.check(fail, s.span, what);
            }
            _ => return Err(Diag::error(s.span, "this statement can't be used here")),
        }
    }
    Ok(())
}

/// Evaluates a right-hand side; tuples are fully evaluated before any assignment.
fn rhs(g: &mut Graph, n: &mut ProcNames, value: &Expr) -> Result<Vec<V>, Diag> {
    match &value.kind {
        ExprKind::Tuple(items) => items.iter().map(|i| lower::expr(g, n, i)).collect(),
        _ => Ok(vec![lower::expr(g, n, value)?]),
    }
}

fn assign(g: &mut Graph, n: &mut ProcNames, target: &Expr, vals: &[V], vspan: Span) -> Result<(), Diag> {
    let names: Vec<&str> = match &target.kind {
        ExprKind::Name(nm) => vec![nm.as_str()],
        ExprKind::Tuple(items) => items
            .iter()
            .map(|i| match &i.kind {
                ExprKind::Name(nm) => Ok(nm.as_str()),
                _ => Err(Diag::error(i.span, "can only assign to names here")),
            })
            .collect::<Result<_, _>>()?,
        _ => return Err(Diag::error(target.span, "can only assign to names here")),
    };
    if names.len() != vals.len() {
        return Err(Diag::error(vspan, format!("can't assign {} value(s) to {} name(s)", vals.len(), names.len())));
    }
    for (name, &v) in names.into_iter().zip(vals) {
        if let Some(s) = n.ctx.states.iter().find(|s| s.name == name) {
            use crate::bundle::Kind;
            let k = crate::bundle::kind(g, v);
            match (s.ty, k) {
                (Ty::Bundle, Kind::Bundle) | (Ty::Int | Ty::Bool, Kind::Int) => {}
                (Ty::Signal, Kind::Signal) => {
                    // A constant signal assigned to a `Signal` variable: its one-hot bundle.
                    let h = g.unsig(v);
                    let sv = g.sigval(h);
                    n.env.insert(name.to_string(), Binding::Val(sv));
                    continue;
                }
                (Ty::Signal, Kind::SigVal) => {}
                (Ty::Bundle, _) => return Err(Diag::error(vspan, format!("{} is a bundle, but this value isn't", crate::expand::quoted(name)))),
                (Ty::Signal, _) => {
                    return Err(Diag::error(vspan, format!("{} is a signal, but this value isn't", crate::expand::quoted(name)))
                        .with_help("signal variables hold one signal, e.g. `S(\"iron-plate\")` or `b.argmax()`"))
                }
                (_, Kind::Bundle) => {
                    return Err(Diag::error(vspan, format!("{} is a number, but this value is a bundle", crate::expand::quoted(name)))
                        .with_help("bundle variables are assigned bundles everywhere; check the other assignments"))
                }
                (_, Kind::Signal | Kind::SigVal) => {
                    return Err(Diag::error(vspan, format!("{} is a number, but this value is a signal", crate::expand::quoted(name)))
                        .with_help("read a signal's value from a bundle with `b[sig]`"))
                }
            }
            if s.ty == Ty::Bool && !g.is_bool(v) {
                return Err(Diag::error(vspan, format!("{} is a bool, but this value can be any int", crate::expand::quoted(name)))
                    .with_help("compare it, e.g. `x != 0`, or use `bool(x)`"));
            }
        }
        n.env.insert(name.to_string(), Binding::Val(v));
    }
    Ok(())
}

type Lowered = (Vec<SrcKind>, Graph, Vec<(usize, V)>);

/// Checks with their conditions fused into deciders; checks that can't fail are dropped.
fn fused_checks(fz: &mut Fuser, raw: Vec<(V, Span, &'static str)>) -> Vec<Check> {
    let mut out = Vec::new();
    for (v, span, what) in raw {
        let fail = fz.rebuild(v);
        if fz.g.as_const(fail) != Some(0) {
            out.push(Check { fail, code: 0, span, what });
        }
    }
    out
}

/// Initial intervals for a process's own state. A bundle's (arrays included) is the interval
/// of its elements, grown by the fixpoint like a number's from its initial elements: e.g.
/// `since = [min(t + 40, 600) for t in since]` keeps them in 40..600, so the comprehension
/// compares `t > 560` instead of computing `t + 40 - 600`.
fn initial_ivs(ctx: &Ctx) -> HashMap<usize, Iv> {
    let elems = |s: &State| s.binit.iter().map(|&(_, v)| Iv::k(v)).reduce(Iv::join).unwrap_or(Iv::k(0));
    ctx.states
        .iter()
        .enumerate()
        .filter(|(_, s)| s.owner == Some(ctx.owner))
        .map(|(si, s)| (si, if s.ty == Ty::Bundle { elems(s) } else { Iv::k(s.init) }))
        .collect()
}

/// Grows `iv` by the given next values; returns whether anything changed. After a few
/// rounds, anything still growing is widened to the full range so the fixpoint terminates.
fn grow(iv: &mut HashMap<usize, Iv>, next: impl Iterator<Item = (usize, Iv)>, round: usize) -> bool {
    let mut changed = false;
    for (si, niv) in next {
        let cur = iv[&si];
        let grown = cur.join(niv);
        if grown != cur {
            changed = true;
            let w = if round >= 4 {
                Iv {
                    lo: if grown.lo < cur.lo { i32::MIN as i64 } else { cur.lo },
                    hi: if grown.hi > cur.hi { i32::MAX as i64 } else { cur.hi },
                }
            } else {
                grown
            };
            iv.insert(si, w);
        }
    }
    changed
}

/// The intervals assumed for a process's own state while lowering it again and again: grown
/// from the initial values until the values written stay within them (widened after a few
/// rounds), then narrowed: widening overshoots (a counter `t = (t + 1) % 6` widens to
/// 0..2^31-1, where `t + 1` could wrap, so `%` keeps its sign correction), so the next
/// assumption is what one round actually writes (plus the initial values), kept while the
/// round after stays within it, which makes it as sound as the widened one.
struct Fixpoint {
    init: HashMap<usize, Iv>,
    iv: HashMap<usize, Iv>,
    /// The last consistent assumption while narrowing (to go back to).
    good: Option<HashMap<usize, Iv>>,
    narrowings: usize,
    done: bool,
}

impl Fixpoint {
    fn new(ctx: &Ctx) -> Self {
        let init = initial_ivs(ctx);
        Fixpoint { iv: init.clone(), init, good: None, narrowings: 0, done: false }
    }

    /// Takes the intervals of the values one round (lowered under `self.iv`) wrote; returns
    /// whether to lower again (under the new `self.iv`).
    fn again(&mut self, next: Vec<(usize, Iv)>, round: usize) -> bool {
        if self.done {
            return false;
        }
        if self.good.is_none() {
            if grow(&mut self.iv, next.iter().copied(), round) {
                return true;
            }
        } else if !next.iter().all(|(si, i)| self.iv[si].contains(*i)) {
            // Not consistent: back to the last assumption that was.
            self.iv = self.good.take().unwrap();
            self.done = true;
            return true;
        }
        let mut tight = self.init.clone();
        for (si, i) in next {
            let t = tight.get_mut(&si).unwrap();
            *t = t.join(i);
        }
        if tight == self.iv || self.narrowings == 3 {
            return false;
        }
        self.narrowings += 1;
        self.good = Some(std::mem::replace(&mut self.iv, tight));
        true
    }
}

/// Lowers an `every` block, iterating to a fixpoint on its state's intervals so that e.g. a
/// counter `x = (x + 1) % 600` is known to stay in 0..599.
fn lower_block(ctx: &Ctx, body: &[Stmt]) -> Result<Lowered, Diag> {
    let mut fp = Fixpoint::new(ctx);
    for round in 0.. {
        let iv = &fp.iv;
        let mut g = Graph::default();
        let mut n = ProcNames { ctx, env: BTreeMap::new(), srcs: Vec::new(), own_iv: iv, live: false, defined: None };
        exec(&mut g, &mut n, body)?;
        let mut next = Vec::new();
        for (si, s) in ctx.states.iter().enumerate() {
            if s.owner == Some(ctx.owner) {
                let v = match n.env.get(&s.name) {
                    Some(Binding::Val(v)) => *v,
                    _ => n.src_for(&mut g, SrcKind::Own(si)),
                };
                next.push((si, g.unsig(v)));
            }
        }
        let srcs = n.srcs;
        let ivs: Vec<(usize, Iv)> = next.iter().map(|(si, v)| (*si, g.iv(*v))).collect();
        if !fp.again(ivs, round) {
            return Ok((srcs, g, next));
        }
    }
    unreachable!()
}

/// Definitely-assigned main variables (without initial values) on entry to each step.
fn definite_assignment(c: &cfg::Cfg) -> Vec<BTreeSet<String>> {
    let n = c.steps.len();
    let musts: Vec<BTreeSet<String>> = c
        .steps
        .iter()
        .map(|d| {
            let mut m = BTreeSet::new();
            must_assign(&d.stmts, &mut m);
            m
        })
        .collect();
    let mut all = BTreeSet::new();
    for m in &musts {
        all.extend(m.iter().cloned());
    }
    // Flow edges. A call flows into the subroutine's entry, and (separately) straight to its
    // continuation together with whatever the subroutine always assigns; returns don't flow
    // back, so one call site's knowledge isn't mixed with another's.
    let mut preds: Vec<Vec<usize>> = vec![Vec::new(); n];
    let mut calls_to: Vec<(usize, String, usize)> = Vec::new(); // (call step, func, cont)
    for (i, d) in c.steps.iter().enumerate() {
        match &d.term {
            Term::Call(f, cont) => {
                preds[c.subs[f]].push(i);
                if let Some(k) = cont {
                    calls_to.push((i, f.clone(), *k));
                }
            }
            Term::Return(_) => {}
            _ => {
                for t in c.successors(i) {
                    preds[t].push(i);
                }
            }
        }
    }
    let returns_of = |f: &str| -> Vec<usize> {
        (0..n).filter(|&i| matches!(&c.steps[i].term, Term::Return(g) if g == f)).collect()
    };
    let mut ins: Vec<BTreeSet<String>> = vec![all.clone(); n];
    ins[c.entry] = BTreeSet::new();
    loop {
        let mut changed = false;
        for i in 0..n {
            if i == c.entry {
                continue;
            }
            let mut acc: Option<BTreeSet<String>> = None;
            let mut meet = |out: BTreeSet<String>| {
                acc = Some(match acc.take() {
                    None => out,
                    Some(a) => a.intersection(&out).cloned().collect(),
                });
            };
            for &p in &preds[i] {
                meet(ins[p].union(&musts[p]).cloned().collect());
            }
            for (call, f, k) in &calls_to {
                if *k == i {
                    // What the subroutine assigns on every path to a return.
                    let mut sub: Option<BTreeSet<String>> = None;
                    for r in returns_of(f) {
                        let out: BTreeSet<String> = ins[r].union(&musts[r]).cloned().collect();
                        sub = Some(match sub {
                            None => out,
                            Some(a) => a.intersection(&out).cloned().collect(),
                        });
                    }
                    let mut out: BTreeSet<String> = ins[*call].union(&musts[*call]).cloned().collect();
                    out.extend(sub.unwrap_or_else(|| all.clone()));
                    meet(out);
                }
            }
            let new = acc.unwrap_or_default();
            if new != ins[i] {
                ins[i] = new;
                changed = true;
            }
        }
        if !changed {
            return ins;
        }
    }
}

/// Register sharing (SPEC §11.2): the process's own variables that are never live at
/// the same time are renamed to one of them, so they share a register. The others are left
/// as states nobody reads (codegen gives those no register). Variables any other process or
/// `every` block mentions and ports keep their own. Bundles with element writes or method
/// receivers are pinned by liveness; whole-bundle assignments may share storage.
/// `TICKY_NO_REGSHARE` turns it off.
/// Returns the renames (variable → the one whose register it shares).
fn share_registers(c: &mut cfg::Cfg, owner: usize, states: &[State], elsewhere: &BTreeSet<&String>) -> BTreeMap<String, String> {
    use crate::liveness::Cand;
    if std::env::var_os("TICKY_NO_REGSHARE").is_some() {
        return BTreeMap::new();
    }
    let cands: BTreeMap<String, Cand> = states
        .iter()
        .filter(|s| s.owner == Some(owner) && s.port.is_none() && !elsewhere.contains(&s.name))
        .filter_map(|s| match s.ty {
            Ty::Int => Some((s.name.clone(), Cand { class: 0, init: s.has_init })),
            Ty::Bool => Some((s.name.clone(), Cand { class: 1, init: s.has_init })),
            Ty::Bundle => Some((s.name.clone(), Cand { class: 2, init: s.has_init })),
            _ => None,
        })
        .collect();
    let map = crate::liveness::coalesce(c, &cands, &definite_assignment(c));
    if map.is_empty() {
        return map;
    }
    if std::env::var_os("TICKY_DUMP_REGSHARE").is_some() {
        eprintln!("register sharing: {map:?}");
    }
    let f = |n: &str| map.get(n).cloned();
    for d in &mut c.steps {
        rename_stmts(&mut d.stmts, &f);
        match &mut d.term {
            Term::Branch(e, ..) | Term::WaitUntil(e, _) | Term::WaitTicks(e, _) => rename_expr(e, &f),
            _ => {}
        }
    }
    map
}

/// Normalize the lowered CFG, where constant folding has exposed additional empty jumps.
/// Checks are observable actions even when the step has no variable writes.
fn simplify_steps(steps: &mut [Step], mut entry: usize) -> usize {
    fn retarget(kind: &mut StepKind, resolve: &impl Fn(Option<usize>) -> Option<usize>) {
        match kind {
            StepKind::Run(Next::Goto(t)) | StepKind::WaitUntil(_, t) | StepKind::WaitTicks(_, t) => *t = resolve(*t),
            StepKind::Run(Next::Branch(_, a, b)) => { *a = resolve(*a); *b = resolve(*b); }
            StepKind::Run(Next::Call { entry, cont, .. }) => {
                *entry = resolve(Some(*entry)).unwrap_or(*entry);
                *cont = resolve(*cont);
            }
            StepKind::Run(Next::Return { .. }) => {}
        }
    }
    loop {
        let resolve = |mut t: Option<usize>| {
            let mut path = Vec::new();
            while let Some(i) = t {
                if let Some(start) = path.iter().position(|&p| p == i) {
                    // Canonicalize empty cycles rather than repeatedly rotating their IDs.
                    return path[start..].iter().copied().min();
                }
                path.push(i);
                match steps[i].kind {
                    StepKind::Run(Next::Goto(n)) if steps[i].writes.is_empty() && steps[i].checks.is_empty() => t = n,
                    _ => break,
                }
            }
            t
        };
        let mut kinds: Vec<_> = steps.iter().map(|s| s.kind.clone()).collect();
        for kind in &mut kinds {
            retarget(kind, &resolve);
            if let StepKind::Run(Next::Branch(_, a, b)) = kind {
                if a == b { *kind = StepKind::Run(Next::Goto(*a)); }
            }
        }
        let next_entry = resolve(Some(entry)).unwrap_or(entry);
        let mut changed = next_entry != entry;
        entry = next_entry;
        for (s, kind) in steps.iter_mut().zip(kinds) {
            changed |= s.kind != kind;
            s.kind = kind;
        }
        // Exact common tails: keep each state's actions and timing, redirect only its
        // incoming edges. Checked states keep their own source location/error identity.
        let mut representatives: Vec<usize> = (0..steps.len()).collect();
        for i in 0..steps.len() {
            if !steps[i].checks.is_empty() { continue; }
            if let Some(j) = (0..i).find(|&j| representatives[j] == j
                && steps[j].checks.is_empty()
                && steps[i].writes == steps[j].writes
                && steps[i].plans == steps[j].plans
                && steps[i].kind == steps[j].kind) {
                representatives[i] = j;
            }
        }
        for s in steps.iter_mut() {
            let old = s.kind.clone();
            retarget(&mut s.kind, &|t| t.map(|i| representatives[i]));
            changed |= old != s.kind;
        }
        changed |= entry != representatives[entry];
        entry = representatives[entry];
        if !changed { return entry; }
    }
}

/// Backward demand for individual process stores. Reads in checks and control flow are
/// always roots; a write's expression is needed only when its destination is live. Using
/// the original expression includes the old value on conditional keep paths.
fn prune_dead_stores(ctx: &Ctx, elsewhere: &BTreeSet<&String>, g: &Graph, srcs: &[SrcKind], steps: &mut [Step]) {
    if std::env::var_os("TICKY_NO_DEAD_STORES").is_some() {
        return;
    }
    // Return slots and expression temporaries are private transport, not externally
    // observable state. Demand follows their consumers (including every continuation
    // of a shared subroutine). Keep other generated state, notably array banks, pinned.
    let private_transport = |name: &str| {
        let local = name.rsplit_once(':').map_or(name, |(_, local)| local);
        local.rsplit_once(".#ret").is_some_and(|(_, suffix)| suffix.bytes().all(|c| c.is_ascii_digit()))
            || local.strip_prefix("#t").is_some_and(|id| !id.is_empty() && id.bytes().all(|c| c.is_ascii_digit()))
    };
    let observable: BTreeSet<usize> = ctx.states.iter().enumerate()
        .filter(|(_, s)| s.port.is_some() || elsewhere.contains(&s.name) || (s.name.contains('#') && !private_transport(&s.name)))
        .map(|(i, _)| i).collect();
    let reads = |roots: &[V]| -> BTreeSet<usize> {
        g.reachable(roots).into_iter().filter_map(|v| match g.op(v) {
            crate::ir::Op::Src(s) => match srcs[*s as usize] {
                SrcKind::Own(si) => Some(si),
                _ => None,
            },
            _ => None,
        }).collect()
    };
    let control: Vec<BTreeSet<usize>> = steps.iter().map(|s| {
        let mut st = s.clone();
        st.plans.clear();
        reads(&st.roots())
    }).collect();
    let uses: Vec<Vec<(usize, BTreeSet<usize>)>> = steps.iter().map(|s|
        s.writes.iter().map(|(si, v)| (*si, reads(&[*v]))).collect()).collect();
    let successors: Vec<Vec<usize>> = steps.iter().map(|s| match &s.kind {
        StepKind::Run(Next::Return { func }) => steps.iter().filter_map(|call| match &call.kind {
            StepKind::Run(Next::Call { func: f, cont, .. }) if f == func => *cont,
            _ => None,
        }).collect(),
        _ => s.targets().into_iter().flatten().collect(),
    }).collect();
    let mut before = vec![BTreeSet::new(); steps.len()];
    loop {
        let mut changed = false;
        for i in (0..steps.len()).rev() {
            let mut after = observable.clone();
            for &j in &successors[i] { after.extend(before[j].iter().copied()); }
            let mut live = after.clone();
            for (si, _) in &uses[i] { live.remove(si); }
            live.extend(control[i].iter().copied());
            for (si, rs) in &uses[i] {
                if after.contains(si) { live.extend(rs.iter().copied()); }
            }
            if before[i] != live { before[i] = live; changed = true; }
        }
        if !changed { break; }
    }
    for (i, step) in steps.iter_mut().enumerate() {
        let mut after = observable.clone();
        for &j in &successors[i] { after.extend(before[j].iter().copied()); }
        step.plans.retain(|(si, _)| after.contains(si));
    }
}

/// Runs the e-graph pass (`egraph.rs`) over a process's lowered steps: their writes, checks,
/// and branch/wait conditions.
fn egraph_steps(g: &mut Graph, steps: &mut [Step], owner: usize) {
    let (mut roots, mut no_const): (Vec<V>, Vec<bool>) = (Vec::new(), Vec::new());
    for s in steps.iter() {
        for (_, v) in &s.writes {
            roots.push(*v);
            no_const.push(false);
        }
        for c in &s.checks {
            roots.push(c.fail);
            no_const.push(true);
        }
        match &s.kind {
            StepKind::Run(Next::Branch(c, ..)) | StepKind::WaitUntil(c, _) => roots.push(c.node),
            StepKind::WaitTicks(WaitN::Dyn(m), _) => roots.push(*m),
            _ => continue,
        }
        no_const.push(true);
    }
    let what = if owner == MAIN { "main".to_string() } else { format!("process {}", MAIN - 1 - owner) };
    let Some(new) = crate::egraph::optimize(g, &roots, &no_const, &what) else { return };
    let mut it = new.into_iter();
    for s in steps.iter_mut() {
        for w in s.writes.iter_mut() {
            w.1 = it.next().unwrap();
        }
        for c in s.checks.iter_mut() {
            c.fail = it.next().unwrap();
        }
        match &mut s.kind {
            StepKind::Run(Next::Branch(c, ..)) | StepKind::WaitUntil(c, _) => c.node = it.next().unwrap(),
            StepKind::WaitTicks(WaitN::Dyn(m), _) => *m = it.next().unwrap(),
            _ => {}
        }
    }
}

fn lower_main(ctx: &Ctx, c: &cfg::Cfg, elsewhere: &BTreeSet<&String>) -> Result<MainProc, Diag> {
    let defined = definite_assignment(c);
    let mut fp = Fixpoint::new(ctx);
    for round in 0.. {
        let iv = &fp.iv;
        timing(&format!("main round {round} ({} steps)", c.steps.len()), crate::clock::Instant::now());
        let mut g = Graph::default();
        let mut srcs = Vec::new();
        let mut steps = Vec::new();
        for (i, d) in c.steps.iter().enumerate() {
            let mut n = ProcNames {
                ctx,
                env: BTreeMap::new(),
                srcs: std::mem::take(&mut srcs),
                own_iv: iv,
                live: false,
                defined: Some(&defined[i]),
            };
            let first_check = g.checks.len();
            exec(&mut g, &mut n, &d.stmts)?;
            let mut writes = Vec::new();
            for (name, b) in &n.env {
                if let (Binding::Val(v), Some(si)) = (b, ctx.states.iter().position(|s| &s.name == name)) {
                    writes.push((si, g.unsig(*v)));
                }
            }
            let kind = match &d.term {
                Term::Open => unreachable!(),
                Term::Goto(t) => StepKind::Run(Next::Goto(*t)),
                Term::Call(f, cont) => StepKind::Run(Next::Call { func: f.clone(), entry: c.subs[f], cont: *cont }),
                Term::Return(f) => StepKind::Run(Next::Return { func: f.clone() }),
                Term::Branch(cond, t, f) => {
                    let v = lower::expr(&mut g, &mut n, cond)?;
                    let v = g.truth(v);
                    match g.as_const(v) {
                        Some(k) => StepKind::Run(Next::Goto(if k != 0 { *t } else { *f })),
                        None => StepKind::Run(Next::Branch(CondPlan { node: v, pos: None, neg: None }, *t, *f)),
                    }
                }
                Term::WaitUntil(cond, t) => {
                    n.live = true;
                    let v = lower::expr(&mut g, &mut n, cond)?;
                    let v = g.truth(v);
                    match g.as_const(v) {
                        Some(k) if k != 0 => StepKind::Run(Next::Goto(*t)),
                        _ => StepKind::WaitUntil(CondPlan { node: v, pos: None, neg: None }, *t),
                    }
                }
                Term::WaitTicks(e, t) => {
                    let v = lower::expr(&mut g, &mut n, e)?;
                    match g.as_const(v) {
                        Some(k) if k <= 0 => StepKind::Run(Next::Goto(*t)),
                        Some(k) => StepKind::WaitTicks(WaitN::Const(k), *t),
                        None => {
                            let two = g.konst(2);
                            StepKind::WaitTicks(WaitN::Dyn(g.ar(ArOp::Sub, v, two)), *t)
                        }
                    }
                }
            };
            srcs = n.srcs;
            let checks = g.checks[first_check..].iter().map(|&(fail, span, what)| Check { fail, code: 0, span, what }).collect();
            steps.push(Step { span: d.span, origin: d.origin.clone(), visits: d.visits, writes, plans: Vec::new(), kind, depth: 0, wait_ready: 0, checks });
        }
        let ivs: Vec<(usize, Iv)> =
            steps.iter().flat_map(|s| s.writes.iter().map(|(si, v)| (*si, g.iv(*v))).collect::<Vec<_>>()).collect();
        if fp.again(ivs, round) {
            continue;
        }
        egraph_steps(&mut g, &mut steps, ctx.owner);
        // Fusion: plans for every write, condition lists for branches and waits.
        {
            let mut fz = Fuser::new(&mut g);
            let mut roots: Vec<V> = Vec::new();
            for s in &steps {
                roots.extend(s.writes.iter().map(|(_, v)| *v).chain(s.checks.iter().map(|c| c.fail)));
                match &s.kind {
                    StepKind::Run(Next::Branch(c, ..)) | StepKind::WaitUntil(c, _) => roots.push(c.node),
                    StepKind::WaitTicks(WaitN::Dyn(m), _) => roots.push(*m),
                    _ => {}
                }
            }
            fz.plan_order_stats(&roots, false);
            let mut tv: Vec<crate::ir_export::Writer> = Vec::new();
            for s in &mut steps {
                if crate::ir_export::on() {
                    tv.push(crate::ir_export::Writer { name: format!("step {}", tv.len()), writes: s.writes.clone(), pre_kind: Some(s.kind.clone()), ..Default::default() });
                }
                for &(si, v) in &s.writes {
                    let own = srcs.iter().position(|k| *k == SrcKind::Own(si)).map(|id| fz.g.src(id as u32));
                    if let Some(p) = fz.writer_plan(v, own) {
                        s.plans.push((si, p));
                    }
                }
                let raw: Vec<(V, Span, &'static str)> = s.checks.iter().map(|c| (c.fail, c.span, c.what)).collect();
                if let Some(w) = tv.last_mut() {
                    w.checks = raw.iter().map(|c| (c.0, fz.rebuild(c.0))).collect(); // memoised: fused_checks gets the same
                }
                s.checks = fused_checks(&mut fz, raw);
                s.kind = match s.kind.clone() {
                    StepKind::Run(Next::Branch(c, a, b)) => StepKind::Run(Next::Branch(fz.cond(c.node), a, b)),
                    StepKind::WaitUntil(c, t) => StepKind::WaitUntil(fz.cond(c.node), t),
                    StepKind::WaitTicks(WaitN::Dyn(m), t) => StepKind::WaitTicks(WaitN::Dyn(fz.rebuild(m)), t),
                    k => k,
                };
            }
            if crate::ir_export::on() {
                crate::ir_export::steps(&mut tv, &steps);
                crate::ir_export::unit(&if ctx.owner == MAIN { "main".to_string() } else { format!("process {}", MAIN - 1 - ctx.owner) }, fz.g, &srcs, ctx.states, ctx.ports, &tv);
            }
        }
        let entry = simplify_steps(&mut steps, c.entry);
        let depths = g.depths();
        let ready = |nodes: Vec<V>| nodes.iter().map(|v| depths[*v as usize]).max().unwrap_or(0);
        for s in &mut steps {
            let mut d = s.plans.iter().map(|(_, p)| p.ready(&depths)).max().unwrap_or(0);
            // Checks are read by the commit decider (and the error deciders), one tick before
            // the commit.
            let checks = ready(s.checks.iter().map(|c| c.fail).collect());
            if !s.checks.is_empty() {
                d = d.max(checks + 1);
            }
            match &s.kind {
                // Branch conditions are read by the next-step deciders on the commit tick.
                StepKind::Run(Next::Branch(c, ..)) => d = d.max(ready(cond_operands(c, true))),
                // Wait conditions are read by the commit decider itself.
                StepKind::WaitUntil(c, _) => s.wait_ready = ready(cond_operands(c, false)).max(checks),
                StepKind::WaitTicks(WaitN::Dyn(m), _) => s.wait_ready = depths[*m as usize].max(checks),
                _ => {}
            }
            s.depth = d;
        }
        // Keep the already determined duration, writes and checks: removing a dead store
        // must not move a later sample, output or runtime error to an earlier tick.
        prune_dead_stores(ctx, elsewhere, &g, &srcs, &mut steps);
        // Drop steps that are no longer reachable.
        let mut keep = vec![false; steps.len()];
        let mut stack = vec![entry];
        while let Some(i) = stack.pop() {
            if std::mem::replace(&mut keep[i], true) {
                continue;
            }
            stack.extend(steps[i].targets().into_iter().flatten());
        }
        let mut new_id = vec![usize::MAX; steps.len()];
        let mut out = Vec::new();
        for (i, s) in steps.into_iter().enumerate() {
            if keep[i] {
                new_id[i] = out.len();
                out.push(s);
            }
        }
        let remap = |t: Option<usize>| t.map(|i| new_id[i]);
        for s in &mut out {
            s.kind = match s.kind.clone() {
                StepKind::Run(Next::Goto(t)) => StepKind::Run(Next::Goto(remap(t))),
                StepKind::Run(Next::Branch(v, a, b)) => StepKind::Run(Next::Branch(v, remap(a), remap(b))),
                StepKind::Run(Next::Call { func, entry, cont }) => {
                    StepKind::Run(Next::Call { func, entry: remap(Some(entry)).unwrap(), cont: remap(cont) })
                }
                StepKind::Run(Next::Return { func }) => StepKind::Run(Next::Return { func }),
                StepKind::WaitUntil(v, t) => StepKind::WaitUntil(v, remap(t)),
                StepKind::WaitTicks(n, t) => StepKind::WaitTicks(n, remap(t)),
            };
        }
        return Ok(MainProc { name: String::new(), owner: ctx.owner, srcs, graph: g, steps: out, entry: new_id[entry], raw: c.raw.clone() });
    }
    unreachable!()
}
