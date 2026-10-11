//! IR → combinators.
//!
//! * Every value lives on its own signal on one shared green **bus** network. A few circuits
//!   (counters) also use small private red networks.
//! * A RUN switch (constant combinator) gates everything. Its rising edge produces a one-tick
//!   ST pulse that loads every register's initial value.
//! * Registers are a "hold" decider (copies its own output back while not loading) plus one
//!   "load" combinator per writer (`next * enable`), all outputting the register's signal.
//!
//! `every` blocks are multi-cycle: a per-block clock produces EI (sample inputs) and, D+1
//! ticks later, ES (commit state), so sources hold still while the D-deep logic settles.
//!
//! The main program is a state machine: PC holds the current step, T counts ticks since the
//! step started, and each step's commit decider fires CM_s (plus the shared ANY) once its logic
//! has settled — or, for waits, once the wait is over. A commit loads that step's variables,
//! the next PC, and fresh samples of the inputs, and restarts T.
//!
//! Layout: this file has the shared types and helpers, the `Cg` builder and the top-level
//! [`codegen`] (control signals, then blocks, processes and ports). `logic.rs`: the logic of
//! step/period blocks; `pipelined.rs`: every-tick blocks; `period.rs`: `every N` block
//! clocks; `procs.rs`: the step machine of processes; `registers.rs`: registers, samples,
//! counters, start-up delays; `bundles.rs`: bundle wires and bundle combinators;
//! `ports.rs`: input/output ports and screens.

mod bundles;
mod logic;
mod period;
mod pipelined;
mod ports;
mod procs;
mod registers;
mod selects;

use std::collections::{HashMap, VecDeque};

use ticky_factorio::*;
use ticky_syntax::{Diag, Span};

use crate::fuse::{is_true, LoadVal};
use crate::ir::{Dnf, Graph, Lit, Op, V};
use crate::program::{Program, SrcKind};

/// A bundle value: everything its producers output, on its own wires (never the bus).
type BRef = usize;

/// Where a value is: a scalar signal on the bus (or a constant), or a bundle.
#[derive(Copy, Clone, Debug)]
enum Ref {
    Op(Operand),
    Bun(BRef),
}

impl Ref {
    fn op(self) -> Operand {
        match self {
            Ref::Op(o) => o,
            Ref::Bun(_) => unreachable!("a bundle where a number is expected"),
        }
    }

    fn sig(self) -> Sig {
        match self.op() {
            Operand::Sig(s) => s,
            Operand::Const(_) => unreachable!("a constant where a signal is required"),
        }
    }

    fn bun(self) -> BRef {
        match self {
            Ref::Bun(b) => b,
            Ref::Op(_) => unreachable!("a number where a bundle is expected"),
        }
    }
}

use bundles::BVal;

pub struct BlockStats {
    pub span: Span,
    pub requested: Option<u32>,
    pub period: u32,
    pub depth: u32,
    pub combinators: usize,
    /// For pipelined blocks: ticks from an input changing to the outputs changing.
    pub latency: Option<u32>,
}

pub struct StepStats {
    pub span: Span,
    /// Human-readable duration, e.g. "3 ticks" or "waits (≥ 2 ticks)".
    pub duration: String,
    /// Branches back to itself (a one-step loop).
    pub self_loop: bool,
}

pub struct MainStats {
    /// `main` or the process's name.
    pub name: String,
    pub steps: Vec<StepStats>,
    pub combinators: usize,
}

/// A wire network to build: its colour and the connectors on it.
#[derive(Clone)]
pub struct NetSpec {
    pub red: bool,
    pub members: Vec<(EntId, Conn)>,
}

pub struct Codegen {
    pub netlist: Netlist,
    /// `nets[0]` is the green bus.
    pub nets: Vec<NetSpec>,
    /// Entity of each port, by port index.
    pub port_ents: Vec<EntId>,
    pub run_switch: EntId,
    pub blocks: Vec<BlockStats>,
    /// Sequential processes, in `Program::procs` order.
    pub procs: Vec<MainStats>,
    pub signals_used: usize,
    /// Each screen's lamps, pixel by pixel.
    pub screen_lamps: Vec<Vec<EntId>>,
    /// Controls: (input port index, its constant combinator).
    pub controls: Vec<(usize, EntId)>,
}

fn c(sig: Sig, cmp: CmpOp, k: i32) -> Cond {
    Cond { first: sig, first_nets: Nets::BOTH, second: Operand::Const(k), second_nets: Nets::BOTH, cmp, and: true }
}

/// `sig op 0`.
fn cnd(sig: Sig, op: CmpOp) -> Cond {
    c(sig, op, 0)
}

fn or(mut cond: Cond) -> Cond {
    cond.and = false;
    cond
}

/// Combinators per logic cluster (each cluster has its own red wire and signal namespace).
const CLUSTER: usize = 250;

/// Decider conditions as OR-of-AND terms.
type CDnf = Vec<Vec<Cond>>;

/// `prefix ∧ (T1 ∨ T2 ∨ …)` as decider conditions (AND binds tighter than OR).
fn distribute(prefix: &[Cond], terms: &CDnf) -> Vec<Cond> {
    let mut out = Vec::new();
    for (i, t) in terms.iter().enumerate() {
        for (j, cond) in prefix.iter().chain(t.iter()).enumerate() {
            let mut cond = cond.clone();
            cond.and = !(j == 0 && i > 0);
            out.push(cond);
        }
    }
    out
}

/// Conjunction of two condition DNFs.
fn cand(a: &CDnf, b: &CDnf) -> CDnf {
    let mut out = Vec::new();
    for x in a {
        for y in b {
            out.push(x.iter().chain(y.iter()).cloned().collect());
        }
    }
    out
}

fn out_const(sig: Sig, k: i32) -> DOut {
    DOut { sig, copy: false, constant: k, nets: Nets::BOTH }
}

fn dec(conds: Vec<Cond>, outputs: Vec<DOut>) -> Kind {
    Kind::Decider(Decider { conds, outputs })
}

fn dec_const(conds: Vec<Cond>, out: Sig, k: i32) -> Kind {
    dec(conds, vec![out_const(out, k)])
}

fn dec_copy(conds: Vec<Cond>, out: Sig) -> Kind {
    dec(conds, vec![DOut { sig: out, copy: true, constant: 1, nets: Nets::BOTH }])
}

fn arith(a: Operand, op: ArOp, b: Operand, out: Sig) -> Kind {
    Kind::Arith(Arith { first: a, first_nets: Nets::BOTH, second: b, second_nets: Nets::BOTH, op, out })
}

struct Cg {
    net: Netlist,
    nets: Vec<NetSpec>,
    pool: VecDeque<Sig>,
    used: usize,
    run: Sig,
    rp: Sig,
    st: Sig,
    /// `warm[i]` is 1 from `i + 1` ticks after RP: taps of a shared start-up delay line.
    warm: Vec<Sig>,
    bvals: Vec<BVal>,
    each: Sig,
    everything: Sig,
    /// With `--checks`: the error code register (the first failed check's code).
    err: Option<Sig>,
}

/// A condition read from the bus only (for combinators whose red input carries a bundle).
fn green(mut c: Cond) -> Cond {
    c.first_nets = Nets::GREEN;
    if let Operand::Sig(_) = c.second {
        c.second_nets = Nets::GREEN;
    }
    c
}

impl Cg {
    /// A combinator that isn't on the bus at all.
    pub(super) fn loose(&mut self, kind: Kind, desc: impl Into<String>) -> EntId {
        let id = self.net.add(kind, Role::Core);
        self.net.entities[id].description = Some(desc.into());
        id
    }

    pub(super) fn on_bus_in(&mut self, e: EntId) {
        self.nets[0].members.push((e, Conn::InGreen));
    }

    pub(super) fn alloc(&mut self) -> Result<Sig, Diag> {
        self.used += 1;
        self.pool.pop_front().ok_or_else(|| {
            Diag::error(Span::default(), "program too large: ran out of signals")
                .with_help("every value currently gets its own signal; signal reuse comes later")
        })
    }

    /// A combinator on the bus (input and output).
    pub(super) fn core(&mut self, kind: Kind, desc: impl Into<String>) -> EntId {
        let id = self.net.add(kind, Role::Core);
        self.net.entities[id].description = Some(desc.into());
        self.nets[0].members.push((id, Conn::InGreen));
        self.nets[0].members.push((id, Conn::OutGreen));
        id
    }

    /// `--checks`: one decider per failing check (`None`: always fails), firing with the
    /// conditions `base` when no earlier check of the same group fails and no error is recorded
    /// yet. It loads the check's code into the error register (and pulses `also`, e.g. a
    /// process's ANY so that it halts).
    pub(super) fn error_deciders(&mut self, base: &[Cond], also: &[(Sig, i32)], fails: &[(Option<Sig>, i32)], what: &str) {
        let Some(e) = self.err else { return };
        for (k, (bad, code)) in fails.iter().enumerate() {
            let mut conds = base.to_vec();
            conds.extend(bad.map(|x| c(x, CmpOp::Ne, 0)));
            for (earlier, _) in &fails[..k] {
                conds.push(self.passes(*earlier));
            }
            conds.push(c(e, CmpOp::Eq, 0));
            let mut outs = vec![out_const(e, *code)];
            outs.extend(also.iter().map(|&(a, k)| out_const(a, k)));
            self.core(dec(conds, outs), format!("{what}: check {code} failed (error code)"));
        }
    }

    /// The condition that a check passes (`None`: never).
    pub(super) fn passes(&self, fail: Option<Sig>) -> Cond {
        match fail {
            Some(x) => c(x, CmpOp::Eq, 0),
            None => c(self.run, CmpOp::Lt, i32::MIN),
        }
    }

    pub(super) fn combinators_since(&self, first: EntId) -> usize {
        self.net.entities[first..].iter().filter(|e| e.kind.is_combinator()).count()
    }
}

/// Where each check's failure condition is (`None`: a constant failure), with its code.
fn fail_sigs(checks: &[crate::program::Check], loc: &dyn Fn(V) -> Ref) -> Vec<(Option<Sig>, i32)> {
    checks
        .iter()
        .map(|ck| match loc(ck.fail).op() {
            Operand::Sig(x) => (Some(x), ck.code),
            Operand::Const(_) => (None, ck.code),
        })
        .collect()
}

fn lit_cond(l: &Lit, loc: &dyn Fn(V) -> Ref) -> Cond {
    Cond { second: loc(l.b).op(), ..c(loc(l.a).sig(), l.op, 0) }
}

fn lits(d: &Dnf, f: &dyn Fn(&Lit) -> Cond) -> CDnf {
    d.iter().map(|t| t.iter().map(f).collect()).collect()
}

/// A runtime signal's one-hot bundle (`SigOf` is only a type marker).
fn through_sig(g: &Graph, mut v: V) -> V {
    while let Op::SigOf(x) = *g.op(v) {
        v = x;
    }
    v
}

/// Where any node is, given the sources and the emitted nodes.
fn locate(g: &Graph, v: V, src: &dyn Fn(u32) -> Ref, nodes: &HashMap<V, Ref>) -> Ref {
    let v = through_sig(g, v);
    match *g.op(v) {
        Op::Const(k) => Ref::Op(Operand::Const(k)),
        Op::Src(s) => src(s),
        _ => nodes[&v],
    }
}

/// Signals that every process can read: state registers, raw input ports and `ticks()`.
struct Shared {
    state_sig: HashMap<usize, Sig>,
    state_bun: HashMap<usize, BRef>,
    input_raw: HashMap<usize, Ref>,
    ticks: Option<Sig>,
}

impl Shared {
    fn state(&self, s: usize) -> Ref {
        match self.state_bun.get(&s) {
            Some(b) => Ref::Bun(*b),
            None => Ref::Op(Operand::Sig(self.state_sig[&s])),
        }
    }

    fn raw(&self, p: &Program, k: SrcKind) -> (Ref, String) {
        match k {
            SrcKind::Input(pi) | SrcKind::LiveInput(pi) => (self.input_raw[&pi], format!("input `{}`", p.ports[pi].name)),
            SrcKind::Foreign(s) | SrcKind::LiveForeign(s) | SrcKind::Own(s) => (self.state(s), p.states[s].display_name()),
            SrcKind::Ticks | SrcKind::LiveTicks => (Ref::Op(Operand::Sig(self.ticks.unwrap())), "ticks()".into()),
        }
    }
}

/// States some process reads, or that drive an output. Others need no register at all.
fn live_states(p: &Program) -> Vec<bool> {
    // Outputs, and screens' banks (`name#b`).
    let screen_bank = |n: &str| n.split_once('#').is_some_and(|(a, b)| b.parse::<usize>().is_ok() && p.screens.iter().any(|s| s.var == a));
    let mut live: Vec<bool> = p.states.iter().map(|s| s.port.is_some() || screen_bank(&s.name)).collect();
    let mut mark = |srcs: &[SrcKind]| {
        for k in srcs {
            if let SrcKind::Own(s) | SrcKind::Foreign(s) | SrcKind::LiveForeign(s) = *k {
                live[s] = true;
            }
        }
    };
    for b in &p.blocks {
        mark(&b.srcs);
    }
    for m in &p.procs {
        mark(&m.srcs);
    }
    live
}

/// Output states of `every tick` blocks that are simply recomputed every tick (one
/// unconditional assignment) and read by no process. They need no register: the output port
/// reads the pipeline directly.
fn combinational(p: &Program, live: &[bool]) -> std::collections::HashSet<usize> {
    let mut read = vec![false; p.states.len()];
    let mut mark = |srcs: &[SrcKind]| {
        for k in srcs {
            if let SrcKind::Own(s) | SrcKind::Foreign(s) | SrcKind::LiveForeign(s) = *k {
                read[s] = true;
            }
        }
    };
    for b in &p.blocks {
        mark(&b.srcs);
    }
    for m in &p.procs {
        mark(&m.srcs);
    }
    let mut out = std::collections::HashSet::new();
    for b in &p.blocks {
        if b.pipe.is_none() {
            continue;
        }
        for (si, plan) in &b.plans {
            // One unconditional load, or constants under conditions (which, for a state nobody
            // reads, always cover every case: keeping the old value would read it).
            let simple = plan.loads.len() == 1 && is_true(&plan.loads[0].guard) && plan.keep.is_none();
            let consts = plan.loads.iter().all(|l| matches!(l.val, LoadVal::Const(_)));
            if live[*si] && (simple || consts) && p.states[*si].port.is_some() && !read[*si] {
                out.insert(*si);
            }
        }
    }
    out
}
pub fn codegen(p: &Program, autostart: bool, outputs_west: bool) -> Result<Codegen, Diag> {
    let t = SignalTable::base();
    let live = live_states(p);
    let comb = combinational(p, &live);
    let run = t.lookup("signal-check").unwrap();
    let mut pool: VecDeque<Sig> = t.internal_pool().into_iter().filter(|s| *s != run).collect();
    let mut first = || pool.pop_front().unwrap();
    // State signals first, so they get the most readable names (letters).
    let mut state_sig: HashMap<usize, Sig> = HashMap::new();
    for (si, s) in p.states.iter().enumerate() {
        if s.owner.is_some() && live[si] && !s.ty.is_bun() && !comb.contains(&si) {
            state_sig.insert(si, first());
        }
    }
    let (rp, st) = (first(), first());
    let mut cg = Cg {
        net: Netlist::default(),
        nets: vec![NetSpec { red: false, members: Vec::new() }],
        pool,
        used: 3 + state_sig.len(),
        run,
        rp,
        st,
        warm: Vec::new(),
        bvals: Vec::new(),
        each: t.special("signal-each"),
        everything: t.special("signal-everything"),
        err: None,
    };
    let mut state_bun: HashMap<usize, BRef> = HashMap::new();
    for (si, s) in p.states.iter().enumerate() {
        if s.owner.is_some() && live[si] && s.ty.is_bun() && !comb.contains(&si) {
            state_bun.insert(si, cg.bnew());
        }
    }

    // RUN switch: RUN=1 plus each block clock's +1.
    let mut clocks: Vec<Option<Sig>> = Vec::new();
    for b in &p.blocks {
        clocks.push(if b.period >= 2 { Some(cg.alloc()?) } else { None });
    }
    let mut run_values = vec![(run, 1)];
    run_values.extend(clocks.iter().flatten().map(|k| (*k, 1)));
    let run_switch = cg.net.add(Kind::Constant(ConstComb { values: run_values, on: autostart }), Role::RunSwitch);
    cg.net.entities[run_switch].description = Some(
        "Ticky RUN switch: turn this constant combinator ON to start the program. Turning it off stops and resets it."
            .into(),
    );
    cg.nets[0].members.push((run_switch, Conn::Green));

    // One ANY signal per process: its step-commit pulse (also emitted by ST).
    let mut anys = Vec::new();
    for _ in &p.procs {
        anys.push(cg.alloc()?);
    }
    cg.core(dec_const(vec![c(run, CmpOp::Ne, 0)], rp, 1), "control: RUN delayed one tick");
    let mut st_outs = vec![out_const(st, 1)];
    st_outs.extend(anys.iter().map(|a| out_const(*a, 1)));
    cg.core(dec(vec![c(run, CmpOp::Ne, 0), c(rp, CmpOp::Eq, 0)], st_outs), "control: start pulse (loads initial values)");
    // `--checks`: the error register (loaded once, by the first failing check) and the lamp.
    if p.error_port.is_some() {
        let e = cg.alloc()?;
        cg.err = Some(e);
        cg.core(dec_copy(vec![c(st, CmpOp::Eq, 0), c(run, CmpOp::Ne, 0)], e), "checks: error code (hold)");
        let lamp = cg.net.add(Kind::Lamp(c(e, CmpOp::Ne, 0), None), Role::ErrorLamp);
        cg.net.entities[lamp].description =
            Some("Ticky error lamp (--checks): lights when a runtime check fails; the `error` output port gives the code.".into());
        cg.nets[0].members.push((lamp, Conn::Green));
    }
    let ticks = if p.uses_ticks() {
        let tk = cg.alloc()?;
        cg.counter(tk, vec![c(rp, CmpOp::Ne, 0)], "ticks() counter");
        Some(tk)
    } else {
        None
    };

    // Input ports.
    let mut port_ents = vec![usize::MAX; p.ports.len()];
    let (input_raw, controls) = ports::input_ports(&mut cg, p, &mut port_ents)?;
    let shared = Shared { state_sig, state_bun, input_raw, ticks };
    // Where combinational outputs are read from.
    let mut comb_ref: HashMap<usize, Ref> = HashMap::new();

    let mut blocks = Vec::new();
    for (bi, b) in p.blocks.iter().enumerate() {
        let first_ent = cg.net.entities.len();
        if let Some(pipe) = &b.pipe {
            let (direct, extra) = pipelined::pipelined_block(&mut cg, p, bi, b, pipe, &shared, &live, &comb)?;
            comb_ref.extend(direct);
            blocks.push(BlockStats {
                span: b.span,
                requested: b.requested,
                period: 1,
                depth: b.depth,
                combinators: cg.combinators_since(first_ent),
                // Input port, the pipeline, a register (or the alignment delay) and the output port.
                latency: Some(pipe.latency + 2 + extra),
            });
            continue;
        }
        blocks.push(period::period_block(&mut cg, p, bi, b, clocks[bi], &shared, &live)?);
    }

    let mut procs = Vec::new();
    for (m, any) in p.procs.iter().zip(&anys) {
        procs.push(procs::main_proc(&mut cg, p, m, &shared, *any, &live)?);
    }

    ports::output_ports(&mut cg, p, &shared, &comb_ref, &mut port_ents, outputs_west);
    let screen_lamps = ports::screens(&mut cg, p, &shared);
    cg.bfinish();

    Ok(Codegen { netlist: cg.net, nets: cg.nets, port_ents, run_switch, blocks, procs, signals_used: cg.used, screen_lamps, controls })
}
