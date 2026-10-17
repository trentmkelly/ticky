//! Machine-readable IR export for translation validation (`tools/validate.py`).
//!
//! With `TICKY_EXPORT_IR=file`, every block and process the compiler lowers is appended to
//! `file` as one JSON line: its graph (every node with its interval), its sources (with
//! the intervals assumed for them), the *rewrite claims* made while it was built, and its
//! writes before and after fusion. Without the variable nothing is recorded, and nothing the
//! compiler emits changes either way: the hooks only observe.
//!
//! A claim is one call of a simplifying constructor (`Graph::ar`, `cmp`, `mux_tf`, `bun`,
//! …, and `lower::floor_div`/`floor_mod`): the operation that was asked for (`req`) and the
//! node it returned (`res`). The node usually isn't the plain operation: constant folding,
//! interval-based decisions, algebraic rewrites and canonicalisation happened in between.
//! Each claim says "`res` computes `req`" (under the path conditions for `//` and `%`); the
//! validator proves it with a solver. Calls nested inside a logged call aren't logged
//! separately: the outer claim covers them. Claims whose result is exactly the operation
//! asked for are only counted (`trivial`). The e-graph pass (`egraph.rs`) adds a claim per
//! root it replaces (`Same`: the old root's value), besides the constructor calls it
//! rebuilds with.
//!
//! The fusion part pairs what lowering produced with what fusion made of it: each state's
//! next value with its plan of guarded loads (and accumulator form, for pipelined blocks),
//! each runtime check's condition with its fused one, each branch/wait condition with its
//! condition lists.

use std::collections::BTreeSet;
use std::io::Write;
use std::sync::{Mutex, OnceLock};

use serde_json::{json, Value};
use ticky_factorio::{ArOp, CmpOp, Sig, SignalTable};

use crate::fuse::{CondPlan, LoadVal, WriterPlan};
use crate::ir::{BLit, BOp, BTerm, Dnf, FOut, Graph, Iv, Lit, Op, V};
use crate::pipeline::Acc;
use crate::program::{Next, SrcKind, Step, StepKind, WaitN};

fn target() -> Option<&'static str> {
    static T: OnceLock<Option<String>> = OnceLock::new();
    T.get_or_init(|| std::env::var("TICKY_EXPORT_IR").ok().filter(|s| !s.is_empty())).as_deref()
}

/// Whether the export is on (`TICKY_EXPORT_IR` is set).
pub fn on() -> bool {
    target().is_some()
}

/// What a constructor call asked for.
#[derive(Clone, Debug)]
pub enum Req {
    /// The plain node (`ar`, `cmp`, `mux_tf`, `dec`, `sel`, `bun`, `bget`, …, `intern_op`).
    Op(Op),
    /// `a if c else b` with Python truthiness of `c` (`Graph::mux`).
    PyMux(V, V, V),
    /// `not v` (`Graph::not`).
    Not(V),
    /// Python truthiness of `v` as 0/1 (`Graph::truth`).
    Truth(V),
    /// Element `i` of an `n`-element array bundle, 0 out of range (`Graph::aget`).
    AGetN(V, V, usize),
    /// Array `b` with element `i` set to `x`, unchanged out of range (`Graph::aset`).
    ASet(V, V, V, usize),
    /// Array `b` with `d` added to element `i` (`Graph::aadd`).
    AAdd(V, V, V, usize),
    /// Bundle `b` with signal `s` set to `x` (`Graph::bset`).
    BSetS(V, Sig, V),
    /// `x` on every slot of array `b` that holds 0 (and nothing elsewhere) (`Graph::azeros`).
    AZeros(V, V, usize),
    /// Python `a // b` (`lower::floor_div`), under the path conditions.
    FloorDiv(V, V, Vec<V>),
    /// Python `a % b` (`lower::floor_mod`), under the path conditions.
    FloorMod(V, V, Vec<V>),
    /// The value of an existing node: an e-graph rewrite of a root (`egraph.rs`), which
    /// replaced node `v` by the claim's result.
    Same(V),
}

/// The rewrite log of one graph.
#[derive(Debug)]
pub struct Log {
    /// Logging the next constructor call (false inside a logged call and when the export is off).
    pub on: bool,
    claims: Vec<(&'static str, Req, V)>,
    trivial: usize,
}

impl Default for Log {
    fn default() -> Self {
        Log { on: on(), claims: Vec::new(), trivial: 0 }
    }
}

/// Logs a constructor call: `tv_hook!(self, "ar", Req::Op(Op::Ar(op, a, b)), self.ar(op, a, b));`
/// as the function's first statement runs the function again with logging off, records what
/// was asked for and what came back, and returns that.
macro_rules! tv_hook {
    ($g:expr, $rule:literal, $req:expr, $call:expr) => {
        if $g.tv.on {
            let req = $req;
            $g.tv.on = false;
            let r = $call;
            $g.tv.on = true;
            $g.tv_claim($rule, req, r);
            return r;
        }
    };
}
pub(crate) use tv_hook;

impl Graph {
    #[doc(hidden)]
    pub fn tv_claim(&mut self, rule: &'static str, req: Req, r: V) {
        if let Req::Op(op) = &req {
            let same = match (op, self.op(r)) {
                (a, b) if a == b => true,
                (Op::Ar(o, a, b), Op::Ar(o2, a2, b2)) => o == o2 && o.commutative() && a == b2 && b == a2,
                (Op::Cmp(o, a, b), Op::Cmp(o2, a2, b2)) => o == o2 && matches!(o, CmpOp::Eq | CmpOp::Ne) && a == b2 && b == a2,
                _ => false,
            };
            if same {
                self.tv.trivial += 1;
                return;
            }
        }
        self.tv.claims.push((rule, req, r));
    }
}

// ------------------------------------------------------------------ JSON

struct J {
    sigs: BTreeSet<u16>,
}

impl J {
    fn sig(&mut self, s: Sig) -> Value {
        self.sigs.insert(s.0);
        json!(s.0)
    }

    fn vals(&mut self, vals: &[(Sig, i32)]) -> Value {
        Value::Array(vals.iter().map(|(s, v)| json!([self.sig(*s), v])).collect())
    }

    fn dnf(&self, d: &Dnf) -> Value {
        Value::Array(d.iter().map(|t| Value::Array(t.iter().map(|l: &Lit| json!([cmp(l.op), l.a, l.b])).collect())).collect())
    }

    fn bdnf(&self, d: &[Vec<BLit>]) -> Value {
        let o = |b: BOp| match b {
            BOp::Each => json!("each"),
            BOp::Val(v) => json!(v),
        };
        Value::Array(d.iter().map(|t| Value::Array(t.iter().map(|l| json!([cmp(l.op), o(l.a), o(l.b)])).collect())).collect())
    }

    fn term(&mut self, t: &BTerm) -> Value {
        let out = |o: &FOut| match o {
            FOut::Copy => Value::Null,
            FOut::Const(k) => json!(k),
        };
        match t {
            BTerm::Map(op, b, k) => json!(["Map", ar(*op), b, k]),
            BTerm::RMap(op, k, b) => json!(["RMap", ar(*op), k, b]),
            BTerm::Zip(op, a, b) => json!(["Zip", ar(*op), a, b]),
            BTerm::ZCmp(op, a, b) => json!(["ZCmp", cmp(*op), a, b]),
            BTerm::One(s, x) => json!(["One", self.sig(*s), x]),
            BTerm::Set(b, s, x) => json!(["Set", b, self.sig(*s), x]),
            BTerm::Filter(b, d, o) => json!(["Filter", b, self.bdnf(d), out(o)]),
            BTerm::DFilter(dom, b, d, o) => json!(["DFilter", dom, b, self.bdnf(d), out(o)]),
            BTerm::K(vals) => json!(["K", self.vals(vals)]),
            BTerm::Shift(s, x, c) => json!(["Shift", self.sig(*s), x, c]),
            BTerm::Hot(t, ix, c) => json!(["Hot", t, ix, c]),
            BTerm::HotEq(t, x, c) => json!(["HotEq", t, x, c]),
            BTerm::Fold(b, op, c, s) => json!(["Fold", b, ar(*op), c, self.sig(*s)]),
            BTerm::Ar(op, a, b, s) => json!(["Ar", ar(*op), a, b, self.sig(*s)]),
            BTerm::Dec(arms) => {
                let arms: Vec<Value> = arms.iter().map(|(d, vals)| json!([self.dnf(d), self.vals(vals)])).collect();
                json!(["Dec", arms])
            }
        }
    }

    fn op(&mut self, op: &Op) -> Value {
        match op {
            Op::Const(k) => json!(["Const", k]),
            Op::Src(s) => json!(["Src", s]),
            Op::Ar(o, a, b) => json!(["Ar", ar(*o), a, b]),
            Op::Cmp(o, a, b) => json!(["Cmp", cmp(*o), a, b]),
            Op::Mux { t, f, a, b } => json!(["Mux", t, f, a, b]),
            Op::Dec(arms) => json!(["Dec", arms.iter().map(|(d, k)| json!([self.dnf(d), k])).collect::<Vec<_>>()]),
            Op::Sel(arms) => json!(["Sel", arms]),
            Op::BConst(vals) => json!(["BConst", self.vals(vals)]),
            Op::Bun(terms) => json!(["Bun", terms.iter().map(|t| self.term(t)).collect::<Vec<_>>()]),
            Op::BMux { t, f, a, b } => json!(["BMux", t, f, a, b]),
            Op::BDec(arms) => json!(["BDec", arms.iter().map(|(d, x)| json!([self.dnf(d), x])).collect::<Vec<_>>()]),
            Op::BSelect(b, max, i) => json!(["BSelect", b, max, i]),
            Op::BGet(b, s) => json!(["BGet", b, self.sig(*s)]),
            Op::BTotal(b) => json!(["BTotal", b]),
            Op::BCount(b) => json!(["BCount", b]),
            Op::AGet(b, ix) => json!(["AGet", b, ix]),
            Op::Each(iv) => json!(["Each", iv.lo, iv.hi]),
            Op::SigK(s) => json!(["SigK", self.sig(*s)]),
            Op::SigOf(x) => json!(["SigOf", x]),
            Op::BSelectAt(b, max, ix) => json!(["BSelectAt", b, max, ix]),
            Op::BDot(a, b) => json!(["BDot", a, b]),
            Op::BSel(b, mode, nonce) => json!(["BSel", b, format!("{mode:?}"), nonce]),
        }
    }

    fn req(&mut self, r: &Req) -> Value {
        match r {
            Req::Op(op) => self.op(op),
            Req::PyMux(c, a, b) => json!(["PyMux", c, a, b]),
            Req::Not(v) => json!(["Not", v]),
            Req::Truth(v) => json!(["Truth", v]),
            Req::AGetN(b, i, n) => json!(["AGetN", b, i, n]),
            Req::ASet(b, i, x, n) => json!(["ASet", b, i, x, n]),
            Req::AAdd(b, i, d, n) => json!(["AAdd", b, i, d, n]),
            Req::BSetS(b, s, x) => json!(["BSetS", b, self.sig(*s), x]),
            Req::AZeros(b, x, n) => json!(["AZeros", b, x, n]),
            Req::FloorDiv(a, b, _) => json!(["FloorDiv", a, b]),
            Req::FloorMod(a, b, _) => json!(["FloorMod", a, b]),
            Req::Same(v) => json!(["Same", v]),
        }
    }

    fn plan(&self, p: &WriterPlan) -> Value {
        let loads: Vec<Value> = p
            .loads
            .iter()
            .map(|l| {
                let val = match l.val {
                    LoadVal::Const(k) => json!(["Const", k]),
                    LoadVal::Node(v) => json!(["Node", v]),
                };
                json!({"guard": self.dnf(&l.guard), "val": val, "direct": l.direct})
            })
            .collect();
        json!({"loads": loads, "keep": p.keep.as_ref().map(|k| self.dnf(k))})
    }

    fn acc(&self, a: &Acc) -> Value {
        json!({
            "w": a.w,
            "consts": a.consts.iter().map(|(d, k)| json!([self.dnf(d), k])).collect::<Vec<_>>(),
            "otherwise": self.dnf(&a.otherwise),
        })
    }

    fn cond(&self, c: &CondPlan) -> Value {
        json!({"node": c.node, "pos": c.pos.as_ref().map(|d| self.dnf(d)), "neg": c.neg.as_ref().map(|d| self.dnf(d))})
    }
}

fn ar(op: ArOp) -> String {
    format!("{op:?}")
}

fn cmp(op: CmpOp) -> String {
    format!("{op:?}")
}

fn iv(i: Iv) -> Value {
    json!([i.lo, i.hi])
}

// ------------------------------------------------------------------ units

/// One writer of a unit: an `every` block's iteration or a main-program step, before and
/// after fusion.
#[derive(Default)]
pub struct Writer {
    pub name: String,
    /// Next values as lowered: (state index, node).
    pub writes: Vec<(usize, V)>,
    /// Fused plans (states updated as accumulators are in `accs` instead).
    pub plans: Vec<(usize, WriterPlan)>,
    pub accs: Vec<(usize, Acc)>,
    /// Runtime checks: (lowered failure condition, fused one).
    pub checks: Vec<(V, V)>,
    /// Branch and wait conditions: (lowered node, fused plan).
    pub conds: Vec<(V, CondPlan)>,
    /// Dynamic waits: (lowered tick count, fused one).
    pub waits: Vec<(V, V)>,
    /// A main-program step's kind before fusion (see [`steps`]).
    pub pre_kind: Option<StepKind>,
}

/// Fills in the plans and the fused branch/wait conditions of main-program steps (`writers`
/// were made, in step order, before fusion).
pub fn steps(writers: &mut [Writer], steps: &[Step]) {
    for (w, s) in writers.iter_mut().zip(steps) {
        w.plans = s.plans.clone();
        match (w.pre_kind.take(), &s.kind) {
            (Some(StepKind::Run(Next::Branch(c0, ..))), StepKind::Run(Next::Branch(c, ..))) | (Some(StepKind::WaitUntil(c0, _)), StepKind::WaitUntil(c, _)) => {
                w.conds.push((c0.node, c.clone()));
            }
            (Some(StepKind::WaitTicks(WaitN::Dyn(m0), _)), StepKind::WaitTicks(WaitN::Dyn(m), _)) => w.waits.push((m0, *m)),
            _ => {}
        }
    }
}

/// The values of every arithmetic and comparison operator on edge cases, as the compiler
/// (and the simulator, which shares `ArOp::apply`/`CmpOp::apply`) computes them, so the
/// validator can check its own encoding against them.
fn probe() -> Value {
    let xs = [i32::MIN, i32::MIN + 1, -65536, -100, -7, -2, -1, 0, 1, 2, 3, 7, 31, 32, 33, 100, 65536, i32::MAX - 1, i32::MAX];
    let ars = [ArOp::Mul, ArOp::Div, ArOp::Add, ArOp::Sub, ArOp::Mod, ArOp::Pow, ArOp::Shl, ArOp::Shr, ArOp::And, ArOp::Or, ArOp::Xor];
    let cmps = [CmpOp::Lt, CmpOp::Gt, CmpOp::Eq, CmpOp::Ge, CmpOp::Le, CmpOp::Ne];
    let mut rows = Vec::new();
    for &a in &xs {
        for &b in &xs {
            for &op in &ars {
                rows.push(json!([ar(op), a, b, op.apply(a, b)]));
            }
            for &op in &cmps {
                rows.push(json!([cmp(op), a, b, op.apply(a, b) as i32]));
            }
        }
    }
    let t = SignalTable::base();
    let slots: Vec<u16> = t.array_signals().iter().map(|s| s.0).collect();
    json!({"ops": rows, "index_signal": t.index_signal().0, "slots": slots})
}

fn emit(line: &Value) {
    static LOCK: Mutex<bool> = Mutex::new(false);
    let Some(path) = target() else { return };
    let mut first = LOCK.lock().unwrap();
    let mut f = std::fs::OpenOptions::new().create(true).append(true).open(path).expect("TICKY_EXPORT_IR: can't open the file");
    if !*first {
        *first = true;
        writeln!(f, "{}", json!({"probe": probe()})).expect("TICKY_EXPORT_IR: write");
    }
    writeln!(f, "{line}").expect("TICKY_EXPORT_IR: write");
}

/// Appends one unit (a block or a process) to the export file.
pub fn unit(name: &str, g: &Graph, srcs: &[SrcKind], states: &[crate::program::State], ports: &[crate::program::Port], writers: &[Writer]) {
    if !on() {
        return;
    }
    let mut j = J { sigs: BTreeSet::new() };
    let state_name = |si: usize| states.get(si).map(|s| s.name.clone()).unwrap_or_default();
    let srcs_j: Vec<Value> = srcs
        .iter()
        .enumerate()
        .map(|(id, k)| {
            let (kind, idx, name) = match *k {
                SrcKind::Own(s) => ("Own", s, state_name(s)),
                SrcKind::Foreign(s) => ("Foreign", s, state_name(s)),
                SrcKind::LiveForeign(s) => ("LiveForeign", s, state_name(s)),
                SrcKind::Input(p) => ("Input", p, ports.get(p).map(|p| p.name.clone()).unwrap_or_default()),
                SrcKind::LiveInput(p) => ("LiveInput", p, ports.get(p).map(|p| p.name.clone()).unwrap_or_default()),
                SrcKind::Ticks => ("Ticks", 0, "ticks()".to_string()),
                SrcKind::LiveTicks => ("LiveTicks", 0, "ticks()".to_string()),
            };
            // Own state's initial value (the validator checks the assumed interval holds
            // from the start, and which signals a bundle register can ever hold).
            let (init, binit) = match *k {
                SrcKind::Own(s) if s < states.len() => (json!(states[s].init), j.vals(&states[s].binit)),
                _ => (Value::Null, Value::Null),
            };
            json!({
                "kind": kind, "index": idx, "name": name,
                "iv": iv(g.src_iv[id]),
                "bun": g.src_bun.get(id).copied().unwrap_or(false),
                "sig": g.src_sig.get(id).copied().unwrap_or(false),
                "init": init, "binit": binit,
            })
        })
        .collect();
    let nodes: Vec<Value> = (0..g.nodes.len() as V).map(|v| json!([j.op(g.op(v)), g.iv(v).lo, g.iv(v).hi, g.is_bundle(v)])).collect();
    let claims: Vec<Value> = g
        .tv
        .claims
        .iter()
        .map(|(rule, req, r)| {
            let path = match req {
                Req::FloorDiv(_, _, p) | Req::FloorMod(_, _, p) => p.clone(),
                _ => Vec::new(),
            };
            json!({"rule": rule, "req": j.req(req), "res": r, "path": path})
        })
        .collect();
    let writers_j: Vec<Value> = writers
        .iter()
        .map(|w| {
            json!({
                "name": w.name,
                "writes": w.writes.iter().map(|(si, v)| json!([si, state_name(*si), v])).collect::<Vec<_>>(),
                "plans": w.plans.iter().map(|(si, p)| json!([si, j.plan(p)])).collect::<Vec<_>>(),
                "accs": w.accs.iter().map(|(si, a)| json!([si, j.acc(a)])).collect::<Vec<_>>(),
                "checks": w.checks,
                "conds": w.conds.iter().map(|(v, c)| json!([v, j.cond(c)])).collect::<Vec<_>>(),
                "waits": w.waits,
            })
        })
        .collect();
    let t = SignalTable::base();
    let sigs: serde_json::Map<String, Value> = j
        .sigs
        .iter()
        .map(|&s| {
            let (a, b, c) = t.rank(Sig(s));
            (s.to_string(), json!([t.name(Sig(s)), [a, b, c]]))
        })
        .collect();
    emit(&json!({
        "unit": name,
        "checks_on": crate::checks_on(),
        "opt_size": crate::opt_size(),
        "srcs": srcs_j,
        "nodes": nodes,
        "claims": claims,
        "trivial": g.tv.trivial,
        "writers": writers_j,
        "sigs": sigs,
    }));
}
