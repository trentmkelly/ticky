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

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum Ty {
    Int,
    Bool,
    Bundle,
}

impl Ty {
    pub fn name(self) -> &'static str {
        match self {
            Ty::Int => "int",
            Ty::Bool => "bool",
            Ty::Bundle => "Bundle",
        }
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
}

impl State {
    /// Hidden loop variables have names that can't be written in source.
    pub fn display_name(&self) -> String {
        if let Some((var, rest)) = self.name.split_once('#') {
            if rest.starts_with('k') || rest.starts_with("end") {
                return format!("loop counter for {}", crate::expand::display(var));
            }
        }
        match crate::expand::display(&self.name) {
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

pub struct Block {
    pub span: Span,
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

#[derive(Clone, Debug)]
pub enum Next {
    /// `None` halts the process.
    Goto(Option<usize>),
    Branch(CondPlan, Option<usize>, Option<usize>),
    /// Jump to a subroutine's entry, recording `cont` as where it returns to.
    Call { func: String, entry: usize, cont: Option<usize> },
    /// Jump back to wherever the subroutine was called from.
    Return { func: String },
}

#[derive(Clone, Debug)]
pub enum WaitN {
    Const(i32),
    /// `n - 2`, compared against the step timer.
    Dyn(V),
}

#[derive(Clone, Debug)]
pub enum StepKind {
    Run(Next),
    WaitUntil(CondPlan, Option<usize>),
    WaitTicks(WaitN, Option<usize>),
}

#[derive(Clone, Debug)]
pub struct Step {
    pub span: Span,
    /// New values of the variables this step assigns.
    pub writes: Vec<(usize, V)>,
    /// How those writes are carried out (after fusion).
    pub plans: Vec<(usize, WriterPlan)>,
    pub kind: StepKind,
    /// Ticks after the step starts until everything committed at its end is ready.
    pub depth: u32,
    /// For waits: ticks after the step starts until the wait condition can be checked.
    pub wait_ready: u32,
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
    pub srcs: Vec<SrcKind>,
    pub graph: Graph,
    pub steps: Vec<Step>,
    pub entry: usize,
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
    pub main: Option<MainProc>,
    pub tests: Vec<TestDef>,
    pub warnings: Vec<Diag>,
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
        self.blocks.iter().any(|b| uses(&b.srcs)) || self.main.as_ref().is_some_and(|m| uses(&m.srcs))
    }
}

fn not_yet(span: Span, what: &str, level: u32) -> Diag {
    Diag::error(span, format!("{what} isn't supported yet (planned for level {level})"))
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
        ExprKind::Name(n) if n == "Signal" => Err(not_yet(e.span, "`Signal`", 6)),
        _ => Err(Diag::error(e.span, "expected a type: `int`, `bool` or `Bundle`")),
    }
}

/// Whether an expression is (syntactically) a bundle, given the names known to be bundles.
fn is_bundle_expr(e: &Expr, bundles: &HashSet<String>) -> bool {
    match &e.kind {
        ExprKind::Dict(_) | ExprKind::DictComp { .. } => true,
        ExprKind::Name(n) => bundles.contains(n),
        ExprKind::Call { func, .. } => matches!(&func.kind, ExprKind::Name(n) if n == "Bundle" || n == "#bset"),
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
    g.as_cv(v).ok_or_else(|| Diag::error(e.span, "expected a constant expression"))
}

/// A constant integer expression.
pub fn eval_int(e: &Expr, consts: &HashMap<String, Cv>, ports: &[Port]) -> Result<i32, Diag> {
    eval_const(e, consts, ports)?.int().ok_or_else(|| Diag::error(e.span, "expected a number"))
}

fn parse_port(table: &SignalTable, s: &Stmt, consts: &HashMap<String, Cv>) -> Result<Port, Diag> {
    let StmtKind::Port { dir, name, ty, signal, label } = &s.kind else { unreachable!() };
    let ty = parse_type(ty)?;
    if ty == Ty::Bundle {
        if let Some((_, sp)) = signal {
            return Err(Diag::error(*sp, "a bundle port carries every signal, so it has no `@ signal`"));
        }
    }
    let sig = match signal {
        _ if ty == Ty::Bundle => table.special("signal-each"),
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
pub fn timing(what: &str, since: std::time::Instant) {
    if std::env::var_os("TICKY_TIMING").is_some() {
        eprintln!("[timing] {what}: {:.1} ms", since.elapsed().as_secs_f64() * 1000.0);
    }
}

pub fn analyze(m: &Module, pipeline: bool) -> Result<Program, Vec<Diag>> {
    let t = std::time::Instant::now();
    let (expanded, (calls, subs)) = crate::expand::expand_module(m)?;
    timing("expand", t);
    let mut p = analyze_expanded(&expanded, pipeline)?;
    timing("analyze", t);
    p.calls = calls;
    p.subroutines = subs;
    Ok(p)
}

fn analyze_expanded(m: &Module, pipeline: bool) -> Result<Program, Vec<Diag>> {
    let t0 = std::time::Instant::now();
    let table = SignalTable::base();
    let mut errs = Vec::new();
    let mut ports: Vec<Port> = Vec::new();
    let mut every: Vec<(&Stmt, Option<&Expr>, &[Stmt])> = Vec::new();
    let mut tests = Vec::new();
    let mut top: Vec<&Stmt> = Vec::new();
    let mut subs: Vec<cfg::SubDef> = Vec::new();

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
            StmtKind::Process { .. } => errs.push(not_yet(s.span, "`process`", 5)),
            StmtKind::Expr(Expr { kind: ExprKind::Str(_), .. }) => {} // docstring
            StmtKind::Sub { name, label, body } => subs.push((name.clone(), *label, body.clone())),
            _ => top.push(s),
        }
    }

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

    // Who assigns what.
    let mut block_assigns: Vec<BTreeMap<String, Span>> = Vec::new();
    for (_, _, body) in &every {
        let mut names = BTreeMap::new();
        assigned_names(body, &mut names, &mut errs);
        block_assigns.push(names);
    }
    let mut main_assigns = BTreeMap::new();
    assigned_names(&main_stmts, &mut main_assigns, &mut errs);
    for (_, _, body) in &subs {
        assigned_names(body, &mut main_assigns, &mut errs);
    }

    let mut consts: HashMap<String, Cv> = HashMap::new();
    for (n, _, _, span) in &pro_order {
        if let Some(p) = ports.iter().find(|p| &p.name == n) {
            if p.dir == PortDir::Input {
                errs.push(Diag::error(*span, format!("`{n}` is an input; inputs can't be assigned")));
            }
            continue;
        }
        if !main_assigns.contains_key(n) && !block_assigns.iter().any(|b| b.contains_key(n)) {
            consts.insert(n.clone(), pro[n].clone());
        }
    }

    let konst = |e: &Expr| eval_int(e, &consts, &ports).ok();
    let main_cfg = if main_stmts.is_empty() {
        None
    } else {
        match cfg::build(&main_stmts, &subs, &konst) {
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

    // Which names hold bundles.
    let mut seed: HashSet<String> = ports.iter().filter(|p| p.ty == Ty::Bundle).map(|p| p.name.clone()).collect();
    seed.extend(pro.iter().filter(|(_, v)| matches!(v, Cv::Bun(_))).map(|(n, _)| n.clone()));
    let mut bodies: Vec<&[Stmt]> = vec![&main_stmts];
    bodies.extend(every.iter().map(|(_, _, b)| *b));
    bodies.extend(subs.iter().map(|(_, _, b)| b.as_slice()));
    let bundles = bundle_names(&bodies, seed);
    let mut nonbool = HashSet::new();
    for b in &bodies {
        nonbool_names(b, &mut nonbool);
    }

    // States: anything assigned by a process, plus outputs.
    let mut states: Vec<State> = Vec::new();
    let mut names: Vec<String> = main_assigns.keys().cloned().collect();
    for b in &block_assigns {
        for n in b.keys() {
            // Names assigned only inside one block with no prologue value are block temporaries.
            let is_port = ports.iter().any(|p| &p.name == n);
            if pro.contains_key(n) || is_port || main_assigns.contains_key(n) {
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
                .or_else(|| block_assigns.iter().find_map(|b| b.get(&n)))
                .copied()
                .unwrap_or(p.span);
            errs.push(Diag::error(span, format!("`{n}` is an input; inputs can't be assigned")));
            continue;
        }
        let mut writers: Vec<(usize, Span)> = Vec::new();
        if let Some(sp) = main_assigns.get(&n) {
            writers.push((MAIN, *sp));
        }
        for (bi, b) in block_assigns.iter().enumerate() {
            if let Some(sp) = b.get(&n) {
                writers.push((bi, *sp));
            }
        }
        if writers.len() > 1 {
            errs.push(Diag::error(writers[1].1, format!("{} is assigned by more than one process", crate::expand::quoted(&n)))
                .with_help("each variable may only be written by one `every` block or by the main program (the single-writer rule); give each its own variable and combine them"));
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
            (Some(Cv::Sig(_)), _) => {
                errs.push(Diag::error(span, format!("{} holds a signal, so it can't be changed while running", crate::expand::quoted(&n)))
                    .with_help("signals that change at runtime come in a later level; use a constant or a bundle"));
            }
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
        });
    }
    if !errs.is_empty() {
        return Err(errs);
    }

    let mut blocks = Vec::new();
    let mut warnings = Vec::new();
    for (bi, (stmt, period, body)) in every.iter().enumerate() {
        let requested = match period {
            None => None,
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
            Ok((srcs, mut graph, next)) => {
                let mut plans = Vec::new();
                let mut fz = Fuser::new(&mut graph);
                for (si, v) in next {
                    let own = srcs.iter().position(|k| *k == SrcKind::Own(si)).map(|id| fz.g.src(id as u32));
                    if let Some(p) = fz.writer_plan(v, own) {
                        plans.push((si, p));
                    }
                }
                let pipe = if pipeline && requested.is_none() { crate::pipeline::plan(&mut graph, &srcs, &mut plans) } else { None };
                let depths = graph.depths();
                let depth = plans.iter().map(|(_, p)| p.ready(&depths)).max().unwrap_or(0);
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
                        if needed > 1 {
                            warnings.push(Diag::warning(header, format!(
                                "this block can only run every {needed} ticks, not every tick"
                            )).with_help(format!(
                                "a value feeds back into itself through {depth} combinators; write `every {needed} ticks:` to make the rate explicit"
                            )));
                        }
                        needed
                    }
                };
                blocks.push(Block { span: stmt.span, requested, srcs, graph, plans, depth, period, pipe });
            }
            Err(d) => errs.push(d),
        }
    }

    timing("blocks", t0);
    let main = match main_cfg {
        Some(c) => {
            let ctx = Ctx { owner: MAIN, ports: &ports, states: &states, consts: &consts };
            match lower_main(&ctx, &c) {
                Ok(m) => Some(m),
                Err(d) => {
                    errs.push(d);
                    None
                }
            }
        }
        None => None,
    };
    if !errs.is_empty() {
        return Err(errs);
    }
    warnings.extend(crate::bundle::take_warnings());
    Ok(Program { calls: Default::default(), subroutines: Default::default(), ports, states, consts, blocks, main, tests, warnings })
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
                    SrcKind::Own(s) | SrcKind::Foreign(s) | SrcKind::LiveForeign(s) => states[s].ty == Ty::Bundle,
                    SrcKind::Input(p) | SrcKind::LiveInput(p) => self.ctx.ports[p].ty == Ty::Bundle,
                    SrcKind::Ticks | SrcKind::LiveTicks => false,
                };
                let iv = match kind {
                    _ if bun => Iv::FULL,
                    SrcKind::Own(s) => self.own_iv[&s],
                    SrcKind::Foreign(s) | SrcKind::LiveForeign(s) if states[s].ty == Ty::Bool => Iv::BOOL,
                    SrcKind::Ticks | SrcKind::LiveTicks => Iv { lo: 0, hi: i32::MAX as i64 },
                    _ => Iv::FULL,
                };
                self.srcs.push(kind);
                g.src_iv.push(iv);
                g.src_bun.push(bun);
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
            let unassigned_main = s.owner == Some(MAIN) && !s.has_init;
            if unassigned_main && self.ctx.owner != MAIN {
                return Err(Diag::error(span, format!("{} is set by the main program, which might not have run yet", crate::expand::quoted(name)))
                    .with_help(format!("give it an initial value at the top of the file, e.g. `{name} = 0`")));
            }
            if unassigned_main && !self.defined.is_some_and(|d| d.contains(name)) {
                return Err(Diag::error(span, format!("{} might be used before it's assigned", crate::expand::quoted(name)))
                    .with_help(format!("assign it first on every path, or give it an initial value at the top of the file, e.g. `{name} = 0`")));
            }
            return Ok(match s.owner {
                Some(o) if o == self.ctx.owner => self.src_for(g, SrcKind::Own(si)),
                Some(_) if self.live => self.src_for(g, SrcKind::LiveForeign(si)),
                Some(_) => self.src_for(g, SrcKind::Foreign(si)),
                None if s.ty == Ty::Bundle => g.bconst(s.binit.iter().copied()),
                None => g.konst(s.init),
            });
        }
        if let Some(pi) = self.ctx.ports.iter().position(|p| p.name == name) {
            let v = self.src_for(g, if self.live { SrcKind::LiveInput(pi) } else { SrcKind::Input(pi) });
            return Ok(if self.ctx.ports[pi].ty == Ty::Bool { g.truth(v) } else { v });
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
                if (ty == Ty::Bundle) != g.is_bundle(v) {
                    return Err(Diag::error(value.span, format!("expected {}", if ty == Ty::Bundle { "a bundle" } else { "a number" })));
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
                    lower::binop(g, *op, cur, rhs)
                };
                assign(g, n, target, &[v], s.span)?;
            }
            StmtKind::If { cond, body, orelse } => {
                let c = lower::expr(g, n, cond)?;
                let c = g.truth(c);
                let before = n.env.clone();
                exec(g, n, body)?;
                let then_env = std::mem::replace(&mut n.env, before.clone());
                exec(g, n, orelse)?;
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
                            if crate::bundle::kind(g, x) != crate::bundle::kind(g, y) {
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
            StmtKind::Assert(_) => return Err(not_yet(s.span, "`assert` in programs", 5)),
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
            match (s.ty == Ty::Bundle, crate::bundle::kind(g, v)) {
                (true, crate::bundle::Kind::Bundle) | (false, crate::bundle::Kind::Int) => {}
                (true, _) => return Err(Diag::error(vspan, format!("{} is a bundle, but this value isn't", crate::expand::quoted(name)))),
                (false, crate::bundle::Kind::Bundle) => {
                    return Err(Diag::error(vspan, format!("{} is a number, but this value is a bundle", crate::expand::quoted(name)))
                        .with_help("bundle variables are assigned bundles everywhere; check the other assignments"))
                }
                (false, crate::bundle::Kind::Signal) => {
                    return Err(Diag::error(vspan, format!("{} can't hold a signal while running", crate::expand::quoted(name)))
                        .with_help("signals that change at runtime come in a later level; use a constant"))
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

/// Initial intervals for a process's own state.
fn initial_ivs(ctx: &Ctx) -> HashMap<usize, Iv> {
    ctx.states
        .iter()
        .enumerate()
        .filter(|(_, s)| s.owner == Some(ctx.owner))
        .map(|(si, s)| (si, if s.ty == Ty::Bundle { Iv::FULL } else { Iv::k(s.init) }))
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

/// Lowers an `every` block, iterating to a fixpoint on its state's intervals so that e.g. a
/// counter `x = (x + 1) % 600` is known to stay in 0..599.
fn lower_block(ctx: &Ctx, body: &[Stmt]) -> Result<Lowered, Diag> {
    let mut iv = initial_ivs(ctx);
    for round in 0.. {
        let mut g = Graph::default();
        let mut n = ProcNames { ctx, env: BTreeMap::new(), srcs: Vec::new(), own_iv: &iv, live: false, defined: None };
        exec(&mut g, &mut n, body)?;
        let mut next = Vec::new();
        for (si, s) in ctx.states.iter().enumerate() {
            if s.owner == Some(ctx.owner) {
                let v = match n.env.get(&s.name) {
                    Some(Binding::Val(v)) => *v,
                    _ => n.src_for(&mut g, SrcKind::Own(si)),
                };
                next.push((si, v));
            }
        }
        let srcs = n.srcs;
        let ivs: Vec<(usize, Iv)> = next.iter().map(|(si, v)| (*si, g.iv(*v))).collect();
        if !grow(&mut iv, ivs.into_iter(), round) {
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

fn lower_main(ctx: &Ctx, c: &cfg::Cfg) -> Result<MainProc, Diag> {
    let defined = definite_assignment(c);
    let mut iv = initial_ivs(ctx);
    for round in 0.. {
        timing(&format!("main round {round} ({} steps)", c.steps.len()), std::time::Instant::now());
        let mut g = Graph::default();
        let mut srcs = Vec::new();
        let mut steps = Vec::new();
        for (i, d) in c.steps.iter().enumerate() {
            let mut n = ProcNames {
                ctx,
                env: BTreeMap::new(),
                srcs: std::mem::take(&mut srcs),
                own_iv: &iv,
                live: false,
                defined: Some(&defined[i]),
            };
            exec(&mut g, &mut n, &d.stmts)?;
            let mut writes = Vec::new();
            for (name, b) in &n.env {
                if let (Binding::Val(v), Some(si)) = (b, ctx.states.iter().position(|s| &s.name == name)) {
                    writes.push((si, *v));
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
            steps.push(Step { span: d.span, writes, plans: Vec::new(), kind, depth: 0, wait_ready: 0 });
        }
        let ivs: Vec<(usize, Iv)> =
            steps.iter().flat_map(|s| s.writes.iter().map(|(si, v)| (*si, g.iv(*v))).collect::<Vec<_>>()).collect();
        if grow(&mut iv, ivs.into_iter(), round) {
            continue;
        }
        // Fusion: plans for every write, condition lists for branches and waits.
        {
            let mut fz = Fuser::new(&mut g);
            for s in &mut steps {
                for &(si, v) in &s.writes {
                    let own = srcs.iter().position(|k| *k == SrcKind::Own(si)).map(|id| fz.g.src(id as u32));
                    if let Some(p) = fz.writer_plan(v, own) {
                        s.plans.push((si, p));
                    }
                }
                s.kind = match s.kind.clone() {
                    StepKind::Run(Next::Branch(c, a, b)) => StepKind::Run(Next::Branch(fz.cond(c.node), a, b)),
                    StepKind::WaitUntil(c, t) => StepKind::WaitUntil(fz.cond(c.node), t),
                    StepKind::WaitTicks(WaitN::Dyn(m), t) => StepKind::WaitTicks(WaitN::Dyn(fz.rebuild(m)), t),
                    k => k,
                };
            }
        }
        let depths = g.depths();
        let ready = |nodes: Vec<V>| nodes.iter().map(|v| depths[*v as usize]).max().unwrap_or(0);
        for s in &mut steps {
            let mut d = s.plans.iter().map(|(_, p)| p.ready(&depths)).max().unwrap_or(0);
            match &s.kind {
                // Branch conditions are read by the next-step deciders on the commit tick.
                StepKind::Run(Next::Branch(c, ..)) => d = d.max(ready(cond_operands(c, true))),
                // Wait conditions are read by the commit decider itself.
                StepKind::WaitUntil(c, _) => s.wait_ready = ready(cond_operands(c, false)),
                StepKind::WaitTicks(WaitN::Dyn(m), _) => s.wait_ready = depths[*m as usize],
                _ => {}
            }
            s.depth = d;
        }
        // Thread jumps through steps that do nothing but jump (e.g. `while True:` headers,
        // whose branch only became a plain jump once its condition was folded).
        let empty = |s: &Step| s.writes.is_empty() && matches!(s.kind, StepKind::Run(Next::Goto(_)));
        let resolve = |mut t: Option<usize>| {
            let mut hops = 0;
            while let Some(i) = t {
                match &steps[i].kind {
                    StepKind::Run(Next::Goto(n)) if empty(&steps[i]) && hops < steps.len() => {
                        t = *n;
                        hops += 1;
                    }
                    _ => break,
                }
            }
            t
        };
        let threaded: Vec<StepKind> = steps
            .iter()
            .map(|s| match s.kind.clone() {
                StepKind::Run(Next::Goto(t)) => StepKind::Run(Next::Goto(resolve(t))),
                StepKind::Run(Next::Branch(v, a, b)) => StepKind::Run(Next::Branch(v, resolve(a), resolve(b))),
                StepKind::Run(Next::Call { func, entry, cont }) => {
                    StepKind::Run(Next::Call { func, entry: resolve(Some(entry)).unwrap_or(entry), cont: resolve(cont) })
                }
                StepKind::Run(Next::Return { func }) => StepKind::Run(Next::Return { func }),
                StepKind::WaitUntil(v, t) => StepKind::WaitUntil(v, resolve(t)),
                StepKind::WaitTicks(n, t) => StepKind::WaitTicks(n, resolve(t)),
            })
            .collect();
        // An entry step that only jumps can be skipped too, unless the jump leads nowhere.
        let entry = match resolve(Some(c.entry)) {
            Some(e) => e,
            None => c.entry,
        };
        for (s, k) in steps.iter_mut().zip(threaded) {
            s.kind = k;
        }

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
        return Ok(MainProc { srcs, graph: g, steps: out, entry: new_id[entry] });
    }
    unreachable!()
}
