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

use std::collections::{HashMap, VecDeque};

use ticky_factorio::*;
use ticky_syntax::ast::PortDir;
use ticky_syntax::{Diag, Span};

use crate::fuse::{is_true, LoadVal, WriterPlan};
use crate::ir::{Dnf, Graph, Lit, Op, V};
use crate::program::{Next, Program, SrcKind, StepKind, WaitN, MAIN};

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
    pub steps: Vec<StepStats>,
    pub combinators: usize,
}

/// A wire network to build: its colour and the connectors on it.
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
    pub main: Option<MainStats>,
    pub signals_used: usize,
}

fn c(sig: Sig, cmp: CmpOp, k: i32) -> Cond {
    Cond { first: sig, first_nets: Nets::BOTH, second: Operand::Const(k), second_nets: Nets::BOTH, cmp, and: true }
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
}

impl Cg {
    fn alloc(&mut self) -> Result<Sig, Diag> {
        self.used += 1;
        self.pool.pop_front().ok_or_else(|| {
            Diag::error(Span::default(), "program too large: ran out of signals")
                .with_help("every value currently gets its own signal; signal reuse comes later")
        })
    }

    /// A combinator on the bus (input and output).
    fn core(&mut self, kind: Kind, desc: impl Into<String>) -> EntId {
        let id = self.net.add(kind, Role::Core);
        self.net.entities[id].description = Some(desc.into());
        self.nets[0].members.push((id, Conn::InGreen));
        self.nets[0].members.push((id, Conn::OutGreen));
        id
    }

    /// `sig` counts up by one every tick while `conds` hold, and is 0 otherwise. A decider
    /// copies the signal from a private red loop that also carries a constant +1.
    fn counter(&mut self, sig: Sig, conds: Vec<Cond>, desc: &str) {
        let d = self.core(dec(conds, vec![DOut { sig, copy: true, constant: 1, nets: Nets::RED }]), desc);
        let k = self.net.add(Kind::Constant(ConstComb { values: vec![(sig, 1)], on: true }), Role::Core);
        self.net.entities[k].description = Some(format!("{desc} (+1)"));
        self.nets.push(NetSpec { red: true, members: vec![(d, Conn::InRed), (d, Conn::OutRed), (k, Conn::Red)] });
    }

    /// Emits combinators for every non-trivial node reachable from `roots`. `src` gives the
    /// signal of each source.
    fn logic(&mut self, g: &Graph, roots: &[V], src: &dyn Fn(u32) -> Sig, what: &str) -> Result<HashMap<V, Sig>, Diag> {
        let live: Vec<V> = g.reachable(roots);
        let producers: Vec<V> =
            live.iter().copied().filter(|v| matches!(g.op(*v), Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) | Op::Sel(_))).collect();

        // Split the logic into clusters of consecutive combinators. A value whose consumers
        // are all in its own cluster lives on that cluster's private red wire, where signal
        // names can be reused; everything else goes on the shared green bus.
        let cluster: HashMap<V, usize> = producers.iter().enumerate().map(|(i, v)| (*v, i / CLUSTER)).collect();
        let is_root: std::collections::HashSet<V> = roots.iter().copied().collect();
        let mut consumers: HashMap<V, Vec<V>> = HashMap::new();
        for &v in &producers {
            for o in g.operands(v) {
                consumers.entry(o).or_default().push(v);
            }
        }
        let local = |v: V| -> bool {
            cluster.contains_key(&v)
                && !is_root.contains(&v)
                && consumers.get(&v).is_some_and(|cs| cs.iter().all(|c| cluster[c] == cluster[&v]))
        };
        let mut node_sig: HashMap<V, Sig> = HashMap::new();
        let mut local_pools: HashMap<usize, VecDeque<Sig>> = HashMap::new();
        for &v in &producers {
            let s = if local(v) {
                let pool = local_pools.entry(cluster[&v]).or_insert_with(|| SignalTable::base().internal_pool().into());
                pool.pop_front().ok_or_else(|| Diag::error(Span::default(), "program too large: a logic cluster ran out of signals"))?
            } else {
                self.alloc()?
            };
            node_sig.insert(v, s);
        }
        let mut cluster_net: HashMap<usize, usize> = HashMap::new();

        for v in producers {
            let out = node_sig[&v];
            let ops = g.operands(v);
            let reads_local = ops.iter().any(|o| local(*o));
            let out_local = local(v);
            // With a red input, every operand must say which wire it comes from.
            let pick = |u: V| -> (Operand, Nets) {
                match *g.op(u) {
                    Op::Const(k) => (Operand::Const(k), Nets::BOTH),
                    Op::Src(s) => (Operand::Sig(src(s)), if reads_local { Nets::GREEN } else { Nets::BOTH }),
                    _ if local(u) => (Operand::Sig(node_sig[&u]), Nets::RED),
                    _ => (Operand::Sig(node_sig[&u]), if reads_local { Nets::GREEN } else { Nets::BOTH }),
                }
            };
            let sig = |u: V| match pick(u) {
                (Operand::Sig(s), n) => (s, n),
                (Operand::Const(_), _) => unreachable!("constant where a signal is required"),
            };
            let cond = |a: V, op: CmpOp, b: V| {
                let ((x, xn), (y, yn)) = (sig(a), pick(b));
                Cond { first: x, first_nets: xn, second: y, second_nets: yn, cmp: op, and: true }
            };
            let ar = |a: V, op: ArOp, b: V| {
                let ((x, xn), (y, yn)) = (pick(a), pick(b));
                Kind::Arith(Arith { first: x, first_nets: xn, second: y, second_nets: yn, op, out })
            };
            let mut kinds: Vec<(Kind, &str)> = Vec::new();
            match *g.op(v) {
                Op::Ar(op, a, b) => kinds.push((ar(a, op, b), "arithmetic")),
                Op::Cmp(op, a, b) => kinds.push((dec_const(vec![cond(a, op, b)], out, 1), "comparison")),
                Op::Mux { .. } | Op::Sel(_) => {
                    let arms: Vec<(V, V)> = match g.op(v) {
                        Op::Mux { t, f, a, b } => vec![(*t, *a), (*f, *b)],
                        Op::Sel(arms) => arms.clone(),
                        _ => unreachable!(),
                    };
                    for (cv, val) in arms {
                        match pick(val).0 {
                            Operand::Const(0) => {}
                            Operand::Const(k) => {
                                let (cs, cn) = sig(cv);
                                let cnd = Cond { first: cs, first_nets: cn, ..c(cs, CmpOp::Ne, 0) };
                                kinds.push((dec_const(vec![cnd], out, k), "select"));
                            }
                            Operand::Sig(_) => kinds.push((ar(val, ArOp::Mul, cv), "select")),
                        }
                    }
                }
                Op::Dec(ref arms) => {
                    for (d, k) in arms {
                        let terms: CDnf = d.iter().map(|t| t.iter().map(|l| cond(l.a, l.op, l.b)).collect()).collect();
                        kinds.push((dec_const(distribute(&[], &terms), out, *k), "condition"));
                    }
                }
                Op::Const(_) | Op::Src(_) => {}
            }
            for (kind, label) in kinds {
                let id = self.net.add(kind, Role::Core);
                self.net.entities[id].description = Some(format!("{what}: {label}"));
                self.nets[0].members.push((id, Conn::InGreen));
                if !out_local {
                    self.nets[0].members.push((id, Conn::OutGreen));
                }
                if reads_local || out_local {
                    let k = cluster[&v];
                    let ni = *cluster_net.entry(k).or_insert_with(|| {
                        self.nets.push(NetSpec { red: true, members: Vec::new() });
                        self.nets.len() - 1
                    });
                    if reads_local {
                        self.nets[ni].members.push((id, Conn::InRed));
                    }
                    if out_local {
                        self.nets[ni].members.push((id, Conn::OutRed));
                    }
                }
            }
        }
        node_sig.retain(|v, _| !local(*v));
        Ok(node_sig)
    }

    /// A register on signal `x`, updated by `writers`. Each writer has a commit pulse `en`
    /// (visible on the commit tick), the conditions that produce that pulse one tick earlier
    /// (`prefix`, used to time enable pulses for guarded loads) and a plan. When no load
    /// fires, the register holds. ST loads `init`.
    fn register(&mut self, x: Sig, init: i32, writers: &[Writer], name: &str) -> Result<(), Diag> {
        let mut hold: CDnf = vec![vec![c(self.st, CmpOp::Eq, 0), c(self.run, CmpOp::Ne, 0)]];
        for w in writers {
            let unconditional = w.plan.loads.len() == 1 && is_true(&w.plan.loads[0].guard);
            let mut factor: CDnf = vec![vec![]];
            if unconditional {
                factor = vec![vec![c(w.en, CmpOp::Eq, 0)]];
            }
            for l in &w.plan.loads {
                if unconditional {
                    match l.val {
                        LoadVal::Const(0) => {}
                        LoadVal::Const(k) => {
                            self.core(dec_const(vec![c(w.en, CmpOp::Ne, 0)], x, k), format!("{name} (load)"));
                        }
                        LoadVal::Node(v) => {
                            let s = (w.sig)(v);
                            self.core(arith(Operand::Sig(s), ArOp::Mul, Operand::Sig(w.en), x), format!("{name} (load)"));
                        }
                    }
                    continue;
                }
                if l.direct {
                    // Checked on the commit tick by the load decider itself.
                    if let LoadVal::Const(k) = l.val {
                        if k != 0 {
                            let guard = lits(&l.guard, w.lit);
                            let conds = distribute(&[c(w.en, CmpOp::Ne, 0)], &guard);
                            self.core(dec_const(conds, x, k), format!("{name} (conditional load)"));
                        }
                    }
                    continue;
                }
                // An enable pulse timed like the commit pulse, but only when the guard holds.
                let eg = self.alloc()?;
                let early = lits(&l.guard, w.lit_eg);
                self.core(dec_const(distribute(&w.prefix, &early), eg, 1), format!("{name} (load condition)"));
                match l.val {
                    LoadVal::Const(0) => {}
                    LoadVal::Const(k) => {
                        self.core(dec_const(vec![c(eg, CmpOp::Ne, 0)], x, k), format!("{name} (conditional load)"));
                    }
                    LoadVal::Node(v) => {
                        let s = (w.sig)(v);
                        self.core(arith(Operand::Sig(s), ArOp::Mul, Operand::Sig(eg), x), format!("{name} (conditional load)"));
                    }
                }
                factor = cand(&factor, &vec![vec![c(eg, CmpOp::Eq, 0)]]);
            }
            if let Some(keep) = &w.plan.keep {
                // Hold unless committing with one of the direct loads' conditions true.
                let mut either: CDnf = vec![vec![c(w.en, CmpOp::Eq, 0)]];
                either.extend(lits(keep, w.lit));
                factor = cand(&factor, &either);
            }
            hold = cand(&hold, &factor);
        }
        self.core(
            Kind::Decider(Decider {
                conds: distribute(&[], &hold),
                outputs: vec![DOut { sig: x, copy: true, constant: 1, nets: Nets::BOTH }],
            }),
            format!("{name} (hold)"),
        );
        if init != 0 {
            self.core(dec_const(vec![c(self.st, CmpOp::Ne, 0)], x, init), format!("{name} (initial value {init})"));
        }
        Ok(())
    }

    /// A sample register: copies `raw` into a new signal whenever `en` fires.
    fn sample(&mut self, raw: Sig, en: Sig, what: &str) -> Result<Sig, Diag> {
        let smp = self.alloc()?;
        self.core(dec_copy(vec![c(en, CmpOp::Eq, 0), c(self.run, CmpOp::Ne, 0)], smp), format!("sample of {what} (hold)"));
        self.core(arith(Operand::Sig(raw), ArOp::Mul, Operand::Sig(en), smp), format!("sample of {what} (load)"));
        Ok(smp)
    }

    /// A signal that turns on `n` ticks (n ≥ 1) after RP does, and off with it.
    fn warm(&mut self, n: usize) -> Result<Sig, Diag> {
        while self.warm.len() < n {
            let prev = self.warm.last().copied().unwrap_or(self.rp);
            let w = self.alloc()?;
            self.core(dec_const(vec![c(prev, CmpOp::Ne, 0)], w, 1), format!("control: start-up delay {}", self.warm.len() + 1));
            self.warm.push(w);
        }
        Ok(self.warm[n - 1])
    }

    fn combinators_since(&self, first: EntId) -> usize {
        self.net.entities[first..].iter().filter(|e| e.kind.is_combinator()).count()
    }
}

/// One writer of a register, as seen by codegen.
struct Writer<'a> {
    en: Sig,
    prefix: Vec<Cond>,
    plan: &'a WriterPlan,
    sig: &'a dyn Fn(V) -> Sig,
    /// Conditions read on the commit tick.
    lit: &'a dyn Fn(&Lit) -> Cond,
    /// Conditions read one tick earlier, by enable deciders.
    lit_eg: &'a dyn Fn(&Lit) -> Cond,
}

fn lit_cond(g: &Graph, l: &Lit, src: &dyn Fn(u32) -> Sig, node_sig: &HashMap<V, Sig>) -> Cond {
    let Operand::Sig(a) = operand(g, l.a, src, node_sig) else { unreachable!("literal with a constant first operand") };
    Cond { second: operand(g, l.b, src, node_sig), ..c(a, l.op, 0) }
}

fn lits(d: &Dnf, f: &dyn Fn(&Lit) -> Cond) -> CDnf {
    d.iter().map(|t| t.iter().map(f).collect()).collect()
}

fn operand(g: &Graph, v: V, src: &dyn Fn(u32) -> Sig, node_sig: &HashMap<V, Sig>) -> Operand {
    match *g.op(v) {
        Op::Const(k) => Operand::Const(k),
        Op::Src(s) => Operand::Sig(src(s)),
        _ => Operand::Sig(node_sig[&v]),
    }
}

/// Signals that every process can read: state registers, raw input ports and `ticks()`.
struct Shared {
    state_sig: HashMap<usize, Sig>,
    input_raw: HashMap<usize, Sig>,
    ticks: Option<Sig>,
}

impl Shared {
    fn raw(&self, p: &Program, k: SrcKind) -> (Sig, String) {
        match k {
            SrcKind::Input(pi) | SrcKind::LiveInput(pi) => (self.input_raw[&pi], format!("input `{}`", p.ports[pi].name)),
            SrcKind::Foreign(s) | SrcKind::LiveForeign(s) | SrcKind::Own(s) => (self.state_sig[&s], p.states[s].display_name()),
            SrcKind::Ticks | SrcKind::LiveTicks => (self.ticks.unwrap(), "ticks()".into()),
        }
    }
}

/// States some process reads, or that drive an output. Others need no register at all.
fn live_states(p: &Program) -> Vec<bool> {
    let mut live: Vec<bool> = p.states.iter().map(|s| s.port.is_some()).collect();
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
    if let Some(m) = &p.main {
        mark(&m.srcs);
    }
    live
}

pub fn codegen(p: &Program, autostart: bool) -> Result<Codegen, Diag> {
    let t = SignalTable::base();
    let live = live_states(p);
    let run = t.lookup("signal-check").unwrap();
    let mut pool: VecDeque<Sig> = t.internal_pool().into_iter().filter(|s| *s != run).collect();
    let mut first = || pool.pop_front().unwrap();
    // State signals first, so they get the most readable names (letters).
    let mut state_sig: HashMap<usize, Sig> = HashMap::new();
    for (si, s) in p.states.iter().enumerate() {
        if s.owner.is_some() && live[si] {
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
    };

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

    let any = if p.main.is_some() { Some(cg.alloc()?) } else { None };
    cg.core(dec_const(vec![c(run, CmpOp::Ne, 0)], rp, 1), "control: RUN delayed one tick");
    let mut st_outs = vec![out_const(st, 1)];
    st_outs.extend(any.map(|a| out_const(a, 1)));
    cg.core(dec(vec![c(run, CmpOp::Ne, 0), c(rp, CmpOp::Eq, 0)], st_outs), "control: start pulse (loads initial values)");
    let ticks = if p.uses_ticks() {
        let tk = cg.alloc()?;
        cg.counter(tk, vec![c(rp, CmpOp::Ne, 0)], "ticks() counter");
        Some(tk)
    } else {
        None
    };

    // Input ports.
    let mut port_ents = vec![usize::MAX; p.ports.len()];
    let mut input_raw: HashMap<usize, Sig> = HashMap::new();
    for (pi, port) in p.ports.iter().enumerate() {
        if port.dir != PortDir::Input {
            continue;
        }
        let raw = cg.alloc()?;
        input_raw.insert(pi, raw);
        let id = cg.net.add(
            arith(Operand::Sig(port.sig), ArOp::Add, Operand::Const(0), raw),
            Role::InputPort { name: port.name.clone(), signal: port.sig },
        );
        let e = &mut cg.net.entities[id];
        e.dir = Dir::East;
        e.description = Some(format!(
            "Ticky input `{}` ({}){}: reads {} from wires connected to this combinator's input (left) side.",
            port.name,
            port.ty.name(),
            port.label.as_ref().map(|l| format!(" \"{l}\"")).unwrap_or_default(),
            t.name(port.sig)
        ));
        cg.nets[0].members.push((id, Conn::OutGreen));
        port_ents[pi] = id;
    }
    let shared = Shared { state_sig, input_raw, ticks };

    let mut blocks = Vec::new();
    for (bi, b) in p.blocks.iter().enumerate() {
        let first_ent = cg.net.entities.len();
        if let Some(pipe) = &b.pipe {
            pipelined_block(&mut cg, p, bi, b, pipe, &shared, &live)?;
            blocks.push(BlockStats {
                span: b.span,
                requested: b.requested,
                period: 1,
                depth: b.depth,
                combinators: cg.combinators_since(first_ent),
                // Input port, then the pipeline, the register and the output port.
                latency: Some(pipe.latency + 3),
            });
            continue;
        }
        let n = b.period as i32;
        let what = format!("block {}", bi + 1);
        let ei = cg.alloc()?;
        let es = cg.alloc()?;
        // Phase (1..=N) at which ES fires; sampling happens at phase 1.
        let phase_es = ((1 + b.depth) % b.period) as i32 + 1;
        // When both pulses share a phase, the very first ES would commit before anything
        // was computed; WARM (set by the first EI) suppresses it.
        let warm = if phase_es == 1 { Some(cg.alloc()?) } else { None };
        let gate = |k: Option<Sig>, phase: i32| -> Vec<Cond> {
            match k {
                Some(k) => vec![c(k, CmpOp::Eq, phase), c(rp, CmpOp::Ne, 0)],
                None => vec![c(rp, CmpOp::Ne, 0)],
            }
        };
        if let Some(k) = clocks[bi] {
            cg.core(dec_copy(vec![c(k, CmpOp::Lt, n), c(rp, CmpOp::Ne, 0)], k), format!("{what}: clock, period {n}"));
        }
        cg.core(dec_const(gate(clocks[bi], 1), ei, 1), format!("{what}: sample pulse"));
        let mut es_conds = gate(clocks[bi], phase_es);
        if let Some(w) = warm {
            cg.core(
                dec_const(vec![c(ei, CmpOp::Ne, 0), c(run, CmpOp::Ne, 0), or(c(w, CmpOp::Ne, 0)), c(run, CmpOp::Ne, 0)], w, 1),
                format!("{what}: warm-up latch"),
            );
            es_conds.push(c(w, CmpOp::Ne, 0));
        }
        let es_prefix = es_conds.clone();
        cg.core(dec_const(es_conds, es, 1), format!("{what}: commit pulse"));

        // Sources: own state is read directly; everything else is sampled at EI.
        let mut src_sig: Vec<Sig> = Vec::new();
        for &kind in &b.srcs {
            let (raw, name) = shared.raw(p, kind);
            src_sig.push(if let SrcKind::Own(_) = kind { raw } else { cg.sample(raw, ei, &format!("{what}: {name}"))? });
        }
        let plans: Vec<&(usize, WriterPlan)> = b.plans.iter().filter(|(si, _)| live[*si]).collect();
        let roots: Vec<V> = plans.iter().flat_map(|(_, p)| p.operands()).collect();
        let src = |s: u32| src_sig[s as usize];
        let node_sig = cg.logic(&b.graph, &roots, &src, &what)?;
        let sig = |v: V| match operand(&b.graph, v, &src, &node_sig) {
            Operand::Sig(s) => s,
            Operand::Const(_) => unreachable!(),
        };
        let lit = |l: &Lit| lit_cond(&b.graph, l, &src, &node_sig);
        for (si, s) in p.states.iter().enumerate() {
            if s.owner != Some(bi) || !live[si] {
                continue;
            }
            let ws: Vec<Writer> = plans
                .iter()
                .filter(|(w, _)| *w == si)
                .map(|(_, plan)| Writer { en: es, prefix: es_prefix.clone(), plan, sig: &sig, lit: &lit, lit_eg: &lit })
                .collect();
            cg.register(shared.state_sig[&si], s.init, &ws, &format!("state {}", s.display_name()))?;
        }
        blocks.push(BlockStats {
            span: b.span,
            requested: b.requested,
            period: b.period,
            depth: b.depth,
            combinators: cg.combinators_since(first_ent),
            latency: None,
        });
    }

    let main = match &p.main {
        Some(m) => Some(main_proc(&mut cg, p, m, &shared, any.unwrap(), &live)?),
        None => None,
    };

    // Output ports: the state's value while running, 0 when stopped.
    for (pi, port) in p.ports.iter().enumerate() {
        if port.dir != PortDir::Output {
            continue;
        }
        let si = p.output_state(pi).unwrap();
        let s = &p.states[si];
        let kind = match shared.state_sig.get(&si) {
            Some(&x) => arith(Operand::Sig(x), ArOp::Mul, Operand::Sig(run), port.sig),
            None => arith(Operand::Sig(run), ArOp::Mul, Operand::Const(s.init), port.sig),
        };
        let id = cg.net.add(kind, Role::OutputPort { name: port.name.clone(), signal: port.sig });
        let e = &mut cg.net.entities[id];
        e.dir = Dir::East;
        e.description = Some(format!(
            "Ticky output `{}` ({}){}: sends {} on wires connected to this combinator's output (right) side.",
            port.name,
            port.ty.name(),
            port.label.as_ref().map(|l| format!(" \"{l}\"")).unwrap_or_default(),
            t.name(port.sig)
        ));
        cg.nets[0].members.push((id, Conn::InGreen));
        port_ents[pi] = id;
    }

    Ok(Codegen { netlist: cg.net, nets: cg.nets, port_ents, run_switch, blocks, main, signals_used: cg.used })
}

/// A block that runs every tick: logic is a balanced pipeline reading inputs directly.
fn pipelined_block(
    cg: &mut Cg,
    p: &Program,
    bi: usize,
    b: &crate::program::Block,
    pipe: &crate::pipeline::Pipe,
    shared: &Shared,
    live: &[bool],
) -> Result<(), Diag> {
    let what = format!("block {}", bi + 1);
    let g = &b.graph;
    let tau = |v: V| pipe.tau[v as usize];
    // Commit only once the pipeline holds values computed from inputs read after the start.
    let en = cg.warm(pipe.latency as usize + 1)?;
    let en_prefix = if pipe.latency == 0 { cg.rp } else { cg.warm(pipe.latency as usize)? };
    let src_sig: Vec<Sig> = b.srcs.iter().map(|k| shared.raw(p, *k).0).collect();

    // Node signals, then combinators with operands delayed to their consumer's iteration.
    let plans: Vec<&(usize, WriterPlan)> = b.plans.iter().filter(|(si, _)| live[*si]).collect();
    let accs: Vec<&(usize, crate::pipeline::Acc)> = pipe.accs.iter().filter(|(si, _)| live[*si]).collect();
    let acc_conds = |a: &crate::pipeline::Acc| -> Vec<V> {
        a.consts.iter().flat_map(|(d, _)| crate::ir::dnf_operands(d)).chain(crate::ir::dnf_operands(&a.otherwise)).collect()
    };
    let mut roots: Vec<V> = plans.iter().flat_map(|(_, p)| p.operands()).collect();
    for (_, a) in &accs {
        roots.push(a.w);
        roots.extend(acc_conds(a));
    }
    let nodes = g.reachable(&roots);
    let mut node_sig: HashMap<V, Sig> = HashMap::new();
    for &v in &nodes {
        if let Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) = g.op(v) {
            node_sig.insert(v, cg.alloc()?);
        }
    }
    let mut delayed: HashMap<(V, i32), Sig> = HashMap::new();
    // The value of `u` for the current iteration, on the wire at offset `at`.
    let mut at = |cg: &mut Cg, u: V, at: i32| -> Result<Operand, Diag> {
        let base = match *g.op(u) {
            Op::Const(k) => return Ok(Operand::Const(k)),
            Op::Src(s) => src_sig[s as usize],
            _ => node_sig[&u],
        };
        let t = tau(u).expect("timed node");
        assert!(t <= at, "pipeline schedule: value needed before it exists");
        let mut cur = base;
        for d in 1..=(at - t) {
            cur = match delayed.get(&(u, t + d)) {
                Some(s) => *s,
                None => {
                    let s = cg.alloc()?;
                    cg.core(arith(Operand::Sig(cur), ArOp::Add, Operand::Const(0), s), format!("{what}: delay"));
                    delayed.insert((u, t + d), s);
                    s
                }
            };
        }
        Ok(Operand::Sig(cur))
    };
    let as_sig = |o: Operand| match o {
        Operand::Sig(s) => s,
        Operand::Const(_) => unreachable!("constant where a signal is required"),
    };
    for &v in &nodes {
        let Some(&out) = node_sig.get(&v) else { continue };
        let t = tau(v).unwrap() - 1;
        match g.op(v).clone() {
            Op::Ar(op, a, bb) => {
                let (x, y) = (at(cg, a, t)?, at(cg, bb, t)?);
                cg.core(arith(x, op, y, out), format!("{what}: arithmetic"));
            }
            Op::Cmp(op, a, bb) => {
                let (x, y) = (as_sig(at(cg, a, t)?), at(cg, bb, t)?);
                cg.core(dec_const(vec![Cond { second: y, ..c(x, op, 0) }], out, 1), format!("{what}: comparison"));
            }
            Op::Mux { .. } | Op::Sel(_) => {
                let arms: Vec<(V, V)> = match g.op(v) {
                    Op::Mux { t, f, a, b } => vec![(*t, *a), (*f, *b)],
                    Op::Sel(arms) => arms.clone(),
                    _ => unreachable!(),
                };
                for (cond, val) in arms {
                    let cs = as_sig(at(cg, cond, t)?);
                    match at(cg, val, t)? {
                        Operand::Const(0) => {}
                        Operand::Const(k) => {
                            cg.core(dec_const(vec![c(cs, CmpOp::Ne, 0)], out, k), format!("{what}: select"));
                        }
                        Operand::Sig(s) => {
                            cg.core(arith(Operand::Sig(s), ArOp::Mul, Operand::Sig(cs), out), format!("{what}: select"));
                        }
                    }
                }
            }
            Op::Dec(arms) => {
                for (d, k) in arms {
                    let mut terms: CDnf = Vec::new();
                    for term in &d {
                        let mut conds = Vec::new();
                        for l in term {
                            let (x, y) = (as_sig(at(cg, l.a, t)?), at(cg, l.b, t)?);
                            conds.push(Cond { second: y, ..c(x, l.op, 0) });
                        }
                        terms.push(conds);
                    }
                    cg.core(dec_const(distribute(&[], &terms), out, k), format!("{what}: condition"));
                }
            }
            Op::Const(_) | Op::Src(_) => {}
        }
    }

    // Loads read values at offset 0; enable deciders read their conditions one tick early.
    let mut ready: HashMap<(V, i32), Operand> = HashMap::new();
    for (_, plan) in &plans {
        for l in &plan.loads {
            let guard_at = if l.direct || is_true(&l.guard) { 0 } else { -1 };
            for v in crate::ir::dnf_operands(&l.guard) {
                ready.insert((v, guard_at), at(cg, v, guard_at)?);
            }
            if let LoadVal::Node(v) = l.val {
                ready.insert((v, 0), at(cg, v, 0)?);
            }
        }
        if let Some(k) = &plan.keep {
            for v in crate::ir::dnf_operands(k) {
                ready.insert((v, 0), at(cg, v, 0)?);
            }
        }
    }
    let mut acc_w: Vec<(usize, Operand)> = Vec::new();
    for (si, a) in &accs {
        acc_w.push((*si, at(cg, a.w, -1)?));
        for v in acc_conds(a) {
            ready.insert((v, 0), at(cg, v, 0)?);
        }
    }
    let sig = |v: V| as_sig(ready[&(v, 0)]);
    let lit_at = |l: &Lit, when: i32| Cond { second: ready[&(l.b, when)], ..c(as_sig(ready[&(l.a, when)]), l.op, 0) };
    let lit = |l: &Lit| lit_at(l, 0);
    let lit_eg = |l: &Lit| lit_at(l, -1);
    for (si, s) in p.states.iter().enumerate() {
        if s.owner != Some(bi) || !live[si] {
            continue;
        }
        let x = shared.state_sig[&si];
        let name = format!("state {}", s.display_name());
        if let Some((_, w)) = acc_w.iter().find(|(a, _)| *a == si) {
            let acc = &accs.iter().find(|(a, _)| *a == si).unwrap().1;
            accumulator(cg, x, s.init, *w, acc, en, &lit, &name);
            continue;
        }
        let ws: Vec<Writer> = plans
            .iter()
            .filter(|(w, _)| *w == si)
            .map(|(_, plan)| Writer { en, prefix: vec![c(en_prefix, CmpOp::Ne, 0)], plan, sig: &sig, lit: &lit, lit_eg: &lit_eg })
            .collect();
        cg.register(x, s.init, &ws, &name)?;
    }
    Ok(())
}

/// `x += w` every tick: the hold decider copies x from a private red loop on which `w`
/// (renamed to x's signal) is also summed.
#[allow(clippy::too_many_arguments)]
fn accumulator(
    cg: &mut Cg,
    x: Sig,
    init: i32,
    w: Operand,
    acc: &crate::pipeline::Acc,
    en: Sig,
    lit: &dyn Fn(&Lit) -> Cond,
    name: &str,
) {
    let (st, run) = (cg.st, cg.run);
    let running = [c(st, CmpOp::Eq, 0), c(run, CmpOp::Ne, 0), c(en, CmpOp::Ne, 0)];
    let hold = cg.core(
        dec(
            distribute(&running, &lits(&acc.otherwise, lit)),
            vec![DOut { sig: x, copy: true, constant: 1, nets: Nets::RED }],
        ),
        format!("{name} (accumulator)"),
    );
    // Constant loads (e.g. a reset) replace the accumulator's output while they apply.
    let mut loads = Vec::new();
    for (d, k) in &acc.consts {
        if *k != 0 {
            let id = cg.core(dec_const(distribute(&[c(en, CmpOp::Ne, 0)], &lits(d, lit)), x, *k), format!("{name} (load)"));
            loads.push(id);
        }
    }
    // Before the block is enabled, hold without adding (copy from the bus, not the loop).
    let idle = cg.core(
        dec(
            vec![c(st, CmpOp::Eq, 0), c(run, CmpOp::Ne, 0), c(en, CmpOp::Eq, 0)],
            vec![DOut { sig: x, copy: true, constant: 1, nets: Nets::GREEN }],
        ),
        format!("{name} (hold while starting)"),
    );
    let mut loop_net = vec![(hold, Conn::InRed), (hold, Conn::OutRed), (idle, Conn::OutRed)];
    loop_net.extend(loads.into_iter().map(|id| (id, Conn::OutRed)));
    if init != 0 {
        let i = cg.core(dec_const(vec![c(st, CmpOp::Ne, 0)], x, init), format!("{name} (initial value {init})"));
        loop_net.push((i, Conn::OutRed));
    }
    // The increment only goes onto the private loop, never the bus.
    let add = cg.net.add(arith(w, ArOp::Add, Operand::Const(0), x), Role::Core);
    cg.net.entities[add].description = Some(format!("{name} (increment)"));
    cg.nets[0].members.push((add, Conn::InGreen));
    loop_net.push((add, Conn::OutRed));
    cg.nets.push(NetSpec { red: true, members: loop_net });
}

fn main_proc(
    cg: &mut Cg,
    p: &Program,
    m: &crate::program::MainProc,
    shared: &Shared,
    any: Sig,
    live: &[bool],
) -> Result<MainStats, Diag> {
    let first_ent = cg.net.entities.len();
    let (run, rp, st) = (cg.run, cg.rp, cg.st);
    let g = &m.graph;
    let pc = cg.alloc()?;
    let tm = cg.alloc()?;
    let pc_of = |s: Option<usize>| s.map_or(0, |i| i as i32 + 1);

    // Step timer: ticks since the current step started.
    cg.counter(tm, vec![c(any, CmpOp::Eq, 0), c(rp, CmpOp::Ne, 0)], "main: step timer");

    // Sources: own variables directly, inputs and other processes' state sampled at each
    // step start, and live (unsampled) versions for `wait until`.
    let mut src_sig: Vec<Sig> = Vec::new();
    for &kind in &m.srcs {
        let (raw, name) = shared.raw(p, kind);
        src_sig.push(match kind {
            SrcKind::Input(_) | SrcKind::Foreign(_) | SrcKind::Ticks => cg.sample(raw, any, &format!("main: {name}"))?,
            _ => raw,
        });
    }
    let src = |s: u32| src_sig[s as usize];
    let mut steps = m.steps.clone();
    for s in &mut steps {
        s.plans.retain(|(si, _)| live[*si]);
    }
    let roots: Vec<V> = steps.iter().flat_map(|s| s.roots()).collect();
    let node_sig = cg.logic(g, &roots, &src, "main")?;
    let opnd = |v: V| operand(g, v, &src, &node_sig);
    let sig_of = |v: V| match opnd(v) {
        Operand::Sig(s) => s,
        Operand::Const(_) => unreachable!(),
    };
    let lit = |l: &Lit| lit_cond(g, l, &src, &node_sig);
    // A condition as decider terms: its condition lists if fused, else `node != 0` / `== 0`.
    let cond_terms = |plan: &crate::fuse::CondPlan, neg: bool| -> CDnf {
        match (if neg { &plan.neg } else { &plan.pos }, &plan.pos, &plan.neg) {
            (Some(d), Some(_), Some(_)) => lits(d, &lit),
            (Some(d), _, _) if !neg => lits(d, &lit),
            _ => vec![vec![c(sig_of(plan.node), if neg { CmpOp::Eq } else { CmpOp::Ne }, 0)]],
        }
    };

    // Commit deciders.
    let mut cm: Vec<Option<(Sig, Vec<Cond>)>> = Vec::new();
    let mut stats = Vec::new();
    for (i, s) in steps.iter().enumerate() {
        let line = format!("main step {}", i + 1);
        let mut prefix = vec![c(pc, CmpOp::Eq, i as i32 + 1), c(any, CmpOp::Eq, 0)];
        let mut extra: CDnf = vec![vec![]];
        // Commits land `depth` ticks after the step starts (at least one), when everything
        // they load is ready: the decider fires one tick before.
        let settle = s.depth.max(1) as i32 - 1;
        let ready = s.wait_ready as i32;
        let duration = match &s.kind {
            StepKind::Run(_) => {
                prefix.push(c(tm, CmpOp::Eq, settle));
                format!("{} ticks", settle + 2)
            }
            StepKind::WaitUntil(plan, _) => {
                let terms = cond_terms(plan, false);
                if terms.is_empty() || g.as_const(plan.node) == Some(0) {
                    cm.push(None);
                    stats.push(StepStats { span: s.span, duration: "waits forever".into(), self_loop: false });
                    continue;
                }
                if ready > 0 {
                    prefix.push(c(tm, CmpOp::Ge, ready));
                }
                extra = terms;
                format!("waits (≥ {} ticks)", ready + 2)
            }
            StepKind::WaitTicks(WaitN::Const(n), _) => {
                prefix.push(c(tm, CmpOp::Eq, (n - 2).max(0)));
                format!("{} ticks", n.max(&2))
            }
            StepKind::WaitTicks(WaitN::Dyn(mv), _) => {
                prefix.push(Cond { second: opnd(*mv), ..c(tm, CmpOp::Ge, 0) });
                if ready > 0 {
                    prefix.push(c(tm, CmpOp::Ge, ready));
                }
                format!("n ticks (≥ {})", ready + 2)
            }
        };
        let cms = cg.alloc()?;
        cg.core(dec(distribute(&prefix, &extra), vec![out_const(cms, 1), out_const(any, 1)]), format!("{line}: commit"));
        cm.push(Some((cms, prefix)));
        let self_loop = s.targets().contains(&Some(i));
        stats.push(StepStats { span: s.span, duration, self_loop });
    }

    // Return-address registers, one per subroutine.
    let mut ret_sig: HashMap<String, Sig> = HashMap::new();
    for s in &steps {
        if let StepKind::Run(Next::Call { func, .. }) = &s.kind {
            if !ret_sig.contains_key(func) {
                let r = cg.alloc()?;
                ret_sig.insert(func.clone(), r);
            }
        }
    }

    // Program counter.
    let mut pc_loads: Vec<Kind> = Vec::new();
    for (i, s) in steps.iter().enumerate() {
        let Some((cms, _)) = &cm[i] else { continue };
        let on = [c(*cms, CmpOp::Ne, 0)];
        match &s.kind {
            StepKind::Run(Next::Goto(t)) | StepKind::WaitUntil(_, t) | StepKind::WaitTicks(_, t) => {
                if t.is_some() {
                    pc_loads.push(dec_const(on.to_vec(), pc, pc_of(*t)));
                }
            }
            StepKind::Run(Next::Branch(plan, a, b)) => {
                for (target, neg) in [(a, false), (b, true)] {
                    let terms = cond_terms(plan, neg);
                    if target.is_some() && !terms.is_empty() {
                        pc_loads.push(dec_const(distribute(&on, &terms), pc, pc_of(*target)));
                    }
                }
            }
            StepKind::Run(Next::Call { entry, .. }) => pc_loads.push(dec_const(on.to_vec(), pc, pc_of(Some(*entry)))),
            // Jump to the step the return-address register holds (if never called, never reached).
            StepKind::Run(Next::Return { func }) => {
                if let Some(&r) = ret_sig.get(func) {
                    pc_loads.push(arith(Operand::Sig(r), ArOp::Mul, Operand::Sig(*cms), pc));
                }
            }
        }
    }
    cg.core(dec_copy(vec![c(any, CmpOp::Eq, 0), c(run, CmpOp::Ne, 0)], pc), "main: program counter (hold)");
    cg.core(dec_const(vec![c(st, CmpOp::Ne, 0)], pc, pc_of(Some(m.entry))), "main: program counter (start)");
    for k in pc_loads {
        cg.core(k, "main: program counter (next step)");
    }

    // Variables.
    for (si, s) in p.states.iter().enumerate() {
        if s.owner != Some(MAIN) || !live[si] {
            continue;
        }
        let mut ws = Vec::new();
        for (i, step) in steps.iter().enumerate() {
            let Some((cms, prefix)) = &cm[i] else { continue };
            for (w, plan) in &step.plans {
                if *w == si {
                    ws.push(Writer { en: *cms, prefix: prefix.clone(), plan, sig: &sig_of, lit: &lit, lit_eg: &lit });
                }
            }
        }
        cg.register(shared.state_sig[&si], s.init, &ws, &format!("variable {}", s.display_name()))?;
    }
    for (func, &r) in &ret_sig {
        let plans: Vec<(Sig, Vec<Cond>, WriterPlan)> = steps
            .iter()
            .enumerate()
            .filter_map(|(i, s)| match (&s.kind, &cm[i]) {
                (StepKind::Run(Next::Call { func: f, cont, .. }), Some((cms, prefix))) if f == func => {
                    let load = crate::fuse::Load { guard: vec![vec![]], val: LoadVal::Const(pc_of(*cont)), direct: false };
                    Some((*cms, prefix.clone(), WriterPlan { loads: vec![load], keep: None }))
                }
                _ => None,
            })
            .collect();
        let ws: Vec<Writer> =
            plans.iter().map(|(en, prefix, plan)| Writer { en: *en, prefix: prefix.clone(), plan, sig: &sig_of, lit: &lit, lit_eg: &lit }).collect();
        cg.register(r, 0, &ws, &format!("main: return address of `{func}`"))?;
    }
    Ok(MainStats { steps: stats, combinators: cg.combinators_since(first_ent) })
}
