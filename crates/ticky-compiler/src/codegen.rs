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
use crate::ir::{BOp, BTerm, Dnf, FOut, Graph, Lit, Op, V};
use crate::program::{Next, Program, SrcKind, StepKind, Ty, WaitN, MAIN};

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

/// The wires of one bundle value. Consumers read it on red (or green, for the second
/// bundle of an element-wise operation); the wire of each colour is made when first needed.
#[derive(Default)]
struct BVal {
    /// Producing entities; `true` for constant combinators (single-sided).
    prods: Vec<(EntId, bool)>,
    red: Option<usize>,
    green: Option<usize>,
}

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
    fn bnew(&mut self) -> BRef {
        self.bvals.push(BVal::default());
        self.bvals.len() - 1
    }

    fn bprod(&mut self, r: BRef, e: EntId) {
        let konst = matches!(self.net.entities[e].kind, Kind::Constant(_));
        self.bvals[r].prods.push((e, konst));
    }

    /// Connects `e`'s red (or green) input to bundle `r`.
    fn bread(&mut self, r: BRef, e: EntId, on_green: bool) {
        let slot = if on_green { self.bvals[r].green } else { self.bvals[r].red };
        let ni = match slot {
            Some(n) => n,
            None => {
                self.nets.push(NetSpec { red: !on_green, members: Vec::new() });
                let n = self.nets.len() - 1;
                if on_green {
                    self.bvals[r].green = Some(n);
                } else {
                    self.bvals[r].red = Some(n);
                }
                n
            }
        };
        self.nets[ni].members.push((e, if on_green { Conn::InGreen } else { Conn::InRed }));
    }

    /// Wires every bundle's producers to the bundle's wires.
    fn bfinish(&mut self) {
        for b in std::mem::take(&mut self.bvals) {
            for (net, red) in [(b.red, true), (b.green, false)] {
                let Some(ni) = net else { continue };
                for &(e, konst) in &b.prods {
                    let conn = match (konst, red) {
                        (true, true) => Conn::Red,
                        (true, false) => Conn::Green,
                        (false, true) => Conn::OutRed,
                        (false, false) => Conn::OutGreen,
                    };
                    self.nets[ni].members.push((e, conn));
                }
            }
        }
    }

    /// A combinator that isn't on the bus at all.
    fn loose(&mut self, kind: Kind, desc: impl Into<String>) -> EntId {
        let id = self.net.add(kind, Role::Core);
        self.net.entities[id].description = Some(desc.into());
        id
    }

    fn on_bus_in(&mut self, e: EntId) {
        self.nets[0].members.push((e, Conn::InGreen));
    }

    /// Combinators for a bundle-valued node, producing bundle `out`. `r` locates operands.
    fn emit_bundle(&mut self, g: &Graph, v: V, out: BRef, r: &dyn Fn(V) -> Ref, what: &str) {
        let each = self.each;
        // A scalar operand of a combinator that reads a bundle on red: from the bus (green).
        let scal = |u: V| -> (Operand, Nets) {
            match r(u).op() {
                Operand::Const(k) => (Operand::Const(k), Nets::BOTH),
                o => (o, Nets::GREEN),
            }
        };
        match g.op(v).clone() {
            Op::BConst(vals) => {
                if !vals.is_empty() {
                    let k = self.loose(Kind::Constant(ConstComb { values: vals, on: true }), format!("{what}: bundle constant"));
                    self.bprod(out, k);
                }
            }
            Op::Bun(terms) => {
                for t in terms {
                    let (kind, reads, bus, label): (Kind, Vec<(V, bool)>, bool, &str) = match t {
                        BTerm::Map(op, b, k) => {
                            let (o, n) = scal(k);
                            let a = Arith { first: Operand::Sig(each), first_nets: Nets::RED, second: o, second_nets: n, op, out: each };
                            (Kind::Arith(a), vec![(b, false)], matches!(o, Operand::Sig(_)), "each with a number")
                        }
                        BTerm::RMap(op, k, b) => {
                            let (o, n) = scal(k);
                            let a = Arith { first: o, first_nets: n, second: Operand::Sig(each), second_nets: Nets::RED, op, out: each };
                            (Kind::Arith(a), vec![(b, false)], matches!(o, Operand::Sig(_)), "number with each")
                        }
                        BTerm::Zip(op, a, b) => {
                            let ar = Arith {
                                first: Operand::Sig(each),
                                first_nets: Nets::RED,
                                second: Operand::Sig(each),
                                second_nets: Nets::GREEN,
                                op,
                                out: each,
                            };
                            (Kind::Arith(ar), vec![(a, false), (b, true)], false, "signal by signal")
                        }
                        BTerm::Pick(b, sig, m) => {
                            let a = arith(Operand::Sig(sig), ArOp::Mul, Operand::Const(m), sig);
                            (a, vec![(b, false)], false, "one signal")
                        }
                        BTerm::One(sig, x) => {
                            let a = arith(r(x).op(), ArOp::Add, Operand::Const(0), sig);
                            (a, vec![], true, "one signal")
                        }
                        BTerm::Filter(b, d, fout) => {
                            let mut conds = Vec::new();
                            for (i, term) in d.iter().enumerate() {
                                let mut lits: Vec<Cond> = Vec::new();
                                for l in term {
                                    let (first, first_nets) = match l.a {
                                        BOp::Each => (each, Nets::RED),
                                        BOp::Val(x) => (r(x).sig(), Nets::GREEN),
                                    };
                                    let (second, second_nets) = match l.b {
                                        BOp::Each => (Operand::Sig(each), Nets::RED),
                                        BOp::Val(x) => scal(x),
                                    };
                                    lits.push(Cond { first, first_nets, second, second_nets, cmp: l.op, and: true });
                                }
                                // Outputting `each` needs `each` in every term's conditions.
                                if !term.iter().any(|l| l.a == BOp::Each || l.b == BOp::Each) {
                                    lits.push(Cond { first: each, first_nets: Nets::RED, second: Operand::Const(0), second_nets: Nets::BOTH, cmp: CmpOp::Ne, and: true });
                                }
                                lits[0].and = i == 0;
                                conds.extend(lits);
                            }
                            let o = match fout {
                                FOut::Copy => DOut { sig: each, copy: true, constant: 1, nets: Nets::RED },
                                FOut::Const(k) => out_const(each, k),
                            };
                            let bus = conds.iter().any(|c| c.first_nets == Nets::GREEN || c.second_nets == Nets::GREEN);
                            (dec(conds, vec![o]), vec![(b, false)], bus, "filter")
                        }
                        BTerm::DFilter(dom, b, d, fout) => {
                            // `each` iterates over the domain (green) and `b` (red): signals
                            // missing from `b` are tested as 0.
                            let mut conds = Vec::new();
                            for (i, term) in d.iter().enumerate() {
                                let mut lits = vec![Cond {
                                    first: each,
                                    first_nets: Nets::GREEN,
                                    second: Operand::Const(0),
                                    second_nets: Nets::BOTH,
                                    cmp: CmpOp::Ne,
                                    and: i == 0,
                                }];
                                for l in term {
                                    let second = match l.b {
                                        BOp::Val(x) => r(x).op(),
                                        BOp::Each => unreachable!("each on both sides"),
                                    };
                                    assert!(matches!(second, Operand::Const(_)), "domain filters compare with constants");
                                    lits.push(Cond { first: each, first_nets: Nets::RED, second, second_nets: Nets::BOTH, cmp: l.op, and: true });
                                }
                                conds.extend(lits);
                            }
                            let o = match fout {
                                FOut::Copy => DOut { sig: each, copy: true, constant: 1, nets: Nets::GREEN },
                                FOut::Const(k) => out_const(each, k),
                            };
                            (dec(conds, vec![o]), vec![(b, false), (dom, true)], false, "filter")
                        }
                        BTerm::K(vals) => {
                            let k = self.loose(Kind::Constant(ConstComb { values: vals, on: true }), format!("{what}: bundle constant"));
                            self.bprod(out, k);
                            continue;
                        }
                    };
                    let id = self.loose(kind, format!("{what}: {label}"));
                    for (b, on_green) in reads {
                        let rb = r(b).bun();
                        self.bread(rb, id, on_green);
                    }
                    if bus {
                        self.on_bus_in(id);
                    }
                    self.bprod(out, id);
                }
            }
            Op::BMux { t, f, a, b } => {
                for (c, x) in [(t, a), (f, b)] {
                    let cond = green(Cond { second: Operand::Const(0), ..cnd(r(c).sig(), CmpOp::Ne) });
                    let id = match g.as_bconst(x) {
                        Some(vals) if vals.is_empty() => continue,
                        Some(vals) => {
                            let outs = vals.iter().map(|(s, k)| out_const(*s, *k)).collect();
                            self.loose(dec(vec![cond], outs), format!("{what}: select"))
                        }
                        None => {
                            let o = DOut { sig: self.everything, copy: true, constant: 1, nets: Nets::RED };
                            let id = self.loose(dec(vec![cond], vec![o]), format!("{what}: select"));
                            let rb = r(x).bun();
                            self.bread(rb, id, false);
                            id
                        }
                    };
                    self.on_bus_in(id);
                    self.bprod(out, id);
                }
            }
            Op::BSelect(b, max) => {
                let id = self.loose(Kind::Selector(Selector::Select { max, index: 0 }), format!("{what}: {}", if max { "largest" } else { "smallest" }));
                let rb = r(b).bun();
                self.bread(rb, id, false);
                self.bprod(out, id);
            }
            _ => unreachable!("not a bundle node"),
        }
    }

    /// Combinators for a scalar read from a bundle (`b[s]`, totals, counts), onto the bus.
    fn emit_from_bundle(&mut self, g: &Graph, v: V, out: Sig, r: &dyn Fn(V) -> Ref, what: &str) {
        let each = self.each;
        let (kind, b, label) = match *g.op(v) {
            Op::BGet(b, s) => (arith(Operand::Sig(s), ArOp::Add, Operand::Const(0), out), b, "read one signal"),
            Op::BTotal(b) => (arith(Operand::Sig(each), ArOp::Add, Operand::Const(0), out), b, "total"),
            Op::BCount(b) => (dec_const(vec![cnd(each, CmpOp::Ne)], out, 1), b, "count"),
            _ => unreachable!("not a bundle read"),
        };
        // Only the bundle is wired to the input, so reading both colours is fine.
        let id = self.loose(kind, format!("{what}: {label}"));
        let rb = r(b).bun();
        self.bread(rb, id, false);
        self.nets[0].members.push((id, Conn::OutGreen));
    }

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

    /// Emits combinators for every non-trivial node reachable from `roots`. `src` locates
    /// each source. Returns where each emitted node's value is.
    fn logic(&mut self, g: &Graph, roots: &[V], src: &dyn Fn(u32) -> Ref, what: &str) -> Result<HashMap<V, Ref>, Diag> {
        let live: Vec<V> = g.reachable(roots);
        let is_scalar_op = |v: V| matches!(g.op(v), Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) | Op::Sel(_));
        let is_read = |v: V| matches!(g.op(v), Op::BGet(..) | Op::BTotal(_) | Op::BCount(_));
        let is_bun_op = |v: V| matches!(g.op(v), Op::BConst(_) | Op::Bun(_) | Op::BMux { .. } | Op::BSelect(..));
        let producers: Vec<V> = live.iter().copied().filter(|v| is_scalar_op(*v) || is_read(*v) || is_bun_op(*v)).collect();

        // Split the logic into clusters of consecutive combinators. A value whose consumers
        // are all in its own cluster lives on that cluster's private red wire, where signal
        // names can be reused; everything else goes on the shared green bus. Values that
        // bundle combinators read must be on the bus (their red input carries the bundle).
        let cluster: HashMap<V, usize> = producers.iter().enumerate().map(|(i, v)| (*v, i / CLUSTER)).collect();
        let is_root: std::collections::HashSet<V> = roots.iter().copied().collect();
        let mut consumers: HashMap<V, Vec<V>> = HashMap::new();
        for &v in &producers {
            for o in g.operands(v) {
                consumers.entry(o).or_default().push(v);
            }
        }
        let local = |v: V| -> bool {
            is_scalar_op(v)
                && !is_root.contains(&v)
                && consumers.get(&v).is_some_and(|cs| cs.iter().all(|c| is_scalar_op(*c) && cluster[c] == cluster[&v]))
        };
        let mut node_ref: HashMap<V, Ref> = HashMap::new();
        let mut local_sig: HashMap<V, Sig> = HashMap::new();
        let mut local_pools: HashMap<usize, VecDeque<Sig>> = HashMap::new();
        for &v in &producers {
            if is_bun_op(v) {
                node_ref.insert(v, Ref::Bun(self.bnew()));
            } else if local(v) {
                let pool = local_pools.entry(cluster[&v]).or_insert_with(|| SignalTable::base().internal_pool().into());
                let s = pool.pop_front().ok_or_else(|| Diag::error(Span::default(), "program too large: a logic cluster ran out of signals"))?;
                local_sig.insert(v, s);
            } else {
                node_ref.insert(v, Ref::Op(Operand::Sig(self.alloc()?)));
            }
        }
        // Where a value is, for combinators that read bundles (never cluster-local values).
        let locate = |u: V| -> Ref {
            match *g.op(u) {
                Op::Const(k) => Ref::Op(Operand::Const(k)),
                Op::Src(s) => src(s),
                _ => node_ref[&u],
            }
        };
        let mut cluster_net: HashMap<usize, usize> = HashMap::new();

        for v in producers {
            if is_bun_op(v) {
                let out = node_ref[&v].bun();
                self.emit_bundle(g, v, out, &locate, what);
                continue;
            }
            if is_read(v) {
                let out = node_ref[&v].sig();
                self.emit_from_bundle(g, v, out, &locate, what);
                continue;
            }
            let out = match local_sig.get(&v) {
                Some(s) => *s,
                None => node_ref[&v].sig(),
            };
            let ops = g.operands(v);
            let reads_local = ops.iter().any(|o| local(*o));
            let out_local = local(v);
            // With a red input, every operand must say which wire it comes from.
            let pick = |u: V| -> (Operand, Nets) {
                match *g.op(u) {
                    Op::Const(k) => (Operand::Const(k), Nets::BOTH),
                    Op::Src(s) => (src(s).op(), if reads_local { Nets::GREEN } else { Nets::BOTH }),
                    _ if local(u) => (Operand::Sig(local_sig[&u]), Nets::RED),
                    _ => (node_ref[&u].op(), if reads_local { Nets::GREEN } else { Nets::BOTH }),
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
                _ => unreachable!("not a scalar operation"),
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
        Ok(node_ref)
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
                            let s = (w.val)(v).sig();
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
                        let s = (w.val)(v).sig();
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

    /// A bundle register: like [`Cg::register`], but the value is a whole bundle on its own
    /// wire. The hold decider copies everything from that wire while no load fires; loads
    /// multiply the new bundle by their enable pulse.
    fn bregister(&mut self, x: BRef, init: &[(Sig, i32)], writers: &[Writer], name: &str) -> Result<(), Diag> {
        let mut hold: CDnf = vec![vec![c(self.st, CmpOp::Eq, 0), c(self.run, CmpOp::Ne, 0)]];
        let each = self.each;
        for w in writers {
            let unconditional = w.plan.loads.len() == 1 && is_true(&w.plan.loads[0].guard);
            let mut factor: CDnf = vec![vec![]];
            for l in &w.plan.loads {
                let LoadVal::Node(v) = l.val else { unreachable!("bundle loads are nodes") };
                let en = if unconditional {
                    factor = vec![vec![c(w.en, CmpOp::Eq, 0)]];
                    w.en
                } else {
                    let eg = self.alloc()?;
                    let early = lits(&l.guard, w.lit_eg);
                    self.core(dec_const(distribute(&w.prefix, &early), eg, 1), format!("{name} (load condition)"));
                    factor = cand(&factor, &vec![vec![c(eg, CmpOp::Eq, 0)]]);
                    eg
                };
                let load = Kind::Arith(Arith {
                    first: Operand::Sig(each),
                    first_nets: Nets::RED,
                    second: Operand::Sig(en),
                    second_nets: Nets::GREEN,
                    op: ArOp::Mul,
                    out: each,
                });
                let id = self.loose(load, format!("{name} (load)"));
                let src = (w.val)(v).bun();
                self.bread(src, id, false);
                self.on_bus_in(id);
                self.bprod(x, id);
            }
            hold = cand(&hold, &factor);
        }
        let conds: Vec<Cond> = distribute(&[], &hold).into_iter().map(green).collect();
        let keep = DOut { sig: self.everything, copy: true, constant: 1, nets: Nets::RED };
        let id = self.loose(dec(conds, vec![keep]), format!("{name} (hold)"));
        self.bread(x, id, false);
        self.on_bus_in(id);
        self.bprod(x, id);
        if !init.is_empty() {
            let outs = init.iter().map(|(s, k)| out_const(*s, *k)).collect();
            let id = self.loose(dec(vec![green(c(self.st, CmpOp::Ne, 0))], outs), format!("{name} (initial value)"));
            self.on_bus_in(id);
            self.bprod(x, id);
        }
        Ok(())
    }

    /// A bundle sample register: copies bundle `raw` whenever `en` fires.
    fn bsample(&mut self, raw: BRef, en: Sig, what: &str) -> BRef {
        let x = self.bnew();
        let each = self.each;
        let keep = DOut { sig: self.everything, copy: true, constant: 1, nets: Nets::RED };
        let hold = self.loose(dec(vec![green(c(en, CmpOp::Eq, 0)), green(c(self.run, CmpOp::Ne, 0))], vec![keep]), format!("sample of {what} (hold)"));
        self.bread(x, hold, false);
        self.on_bus_in(hold);
        self.bprod(x, hold);
        let load = Kind::Arith(Arith {
            first: Operand::Sig(each),
            first_nets: Nets::RED,
            second: Operand::Sig(en),
            second_nets: Nets::GREEN,
            op: ArOp::Mul,
            out: each,
        });
        let id = self.loose(load, format!("sample of {what} (load)"));
        self.bread(raw, id, false);
        self.on_bus_in(id);
        self.bprod(x, id);
        x
    }

    /// Samples a source: scalar or bundle.
    fn sample_ref(&mut self, raw: Ref, en: Sig, what: &str) -> Result<Ref, Diag> {
        Ok(match raw {
            Ref::Op(Operand::Sig(s)) => Ref::Op(Operand::Sig(self.sample(s, en, what)?)),
            Ref::Bun(b) => Ref::Bun(self.bsample(b, en, what)),
            Ref::Op(Operand::Const(_)) => unreachable!("sampling a constant"),
        })
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
    /// Where a load's value is.
    val: &'a dyn Fn(V) -> Ref,
    /// Conditions read on the commit tick.
    lit: &'a dyn Fn(&Lit) -> Cond,
    /// Conditions read one tick earlier, by enable deciders.
    lit_eg: &'a dyn Fn(&Lit) -> Cond,
}

fn lit_cond(l: &Lit, loc: &dyn Fn(V) -> Ref) -> Cond {
    Cond { second: loc(l.b).op(), ..c(loc(l.a).sig(), l.op, 0) }
}

fn lits(d: &Dnf, f: &dyn Fn(&Lit) -> Cond) -> CDnf {
    d.iter().map(|t| t.iter().map(f).collect()).collect()
}

/// Where any node is, given the sources and the emitted nodes.
fn locate(g: &Graph, v: V, src: &dyn Fn(u32) -> Ref, nodes: &HashMap<V, Ref>) -> Ref {
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
    if let Some(m) = &p.main {
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

pub fn codegen(p: &Program, autostart: bool) -> Result<Codegen, Diag> {
    let t = SignalTable::base();
    let live = live_states(p);
    let comb = combinational(p, &live);
    let run = t.lookup("signal-check").unwrap();
    let mut pool: VecDeque<Sig> = t.internal_pool().into_iter().filter(|s| *s != run).collect();
    let mut first = || pool.pop_front().unwrap();
    // State signals first, so they get the most readable names (letters).
    let mut state_sig: HashMap<usize, Sig> = HashMap::new();
    for (si, s) in p.states.iter().enumerate() {
        if s.owner.is_some() && live[si] && s.ty != Ty::Bundle && !comb.contains(&si) {
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
    };
    let mut state_bun: HashMap<usize, BRef> = HashMap::new();
    for (si, s) in p.states.iter().enumerate() {
        if s.owner.is_some() && live[si] && s.ty == Ty::Bundle && !comb.contains(&si) {
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
    let mut input_raw: HashMap<usize, Ref> = HashMap::new();
    for (pi, port) in p.ports.iter().enumerate() {
        if port.dir != PortDir::Input {
            continue;
        }
        let bundle = port.ty == Ty::Bundle;
        let (kind, raw) = if bundle {
            // Copies everything on the player's wires onto the program's own bundle wire.
            (arith(Operand::Sig(cg.each), ArOp::Add, Operand::Const(0), cg.each), Ref::Bun(cg.bnew()))
        } else {
            let raw = cg.alloc()?;
            (arith(Operand::Sig(port.sig), ArOp::Add, Operand::Const(0), raw), Ref::Op(Operand::Sig(raw)))
        };
        input_raw.insert(pi, raw);
        let id = cg.net.add(kind, Role::InputPort { name: port.name.clone(), signal: port.sig });
        let reads = if bundle { "every signal".to_string() } else { t.name(port.sig).to_string() };
        let e = &mut cg.net.entities[id];
        e.dir = Dir::East;
        e.description = Some(format!(
            "Ticky input `{}` ({}){}: reads {reads} from wires connected to this combinator's input (left) side.",
            port.name,
            port.ty.name(),
            port.label.as_ref().map(|l| format!(" \"{l}\"")).unwrap_or_default(),
        ));
        match raw {
            Ref::Bun(b) => cg.bprod(b, id),
            _ => cg.nets[0].members.push((id, Conn::OutGreen)),
        }
        port_ents[pi] = id;
    }
    let shared = Shared { state_sig, state_bun, input_raw, ticks };
    // Where combinational outputs are read from.
    let mut comb_ref: HashMap<usize, Ref> = HashMap::new();

    let mut blocks = Vec::new();
    for (bi, b) in p.blocks.iter().enumerate() {
        let first_ent = cg.net.entities.len();
        if let Some(pipe) = &b.pipe {
            let (direct, extra) = pipelined_block(&mut cg, p, bi, b, pipe, &shared, &live, &comb)?;
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
        let mut src_ref: Vec<Ref> = Vec::new();
        for &kind in &b.srcs {
            let (raw, name) = shared.raw(p, kind);
            src_ref.push(if let SrcKind::Own(_) = kind { raw } else { cg.sample_ref(raw, ei, &format!("{what}: {name}"))? });
        }
        let plans: Vec<&(usize, WriterPlan)> = b.plans.iter().filter(|(si, _)| live[*si]).collect();
        let roots: Vec<V> = plans.iter().flat_map(|(_, p)| p.operands()).collect();
        let src = |s: u32| src_ref[s as usize];
        let nodes = cg.logic(&b.graph, &roots, &src, &what)?;
        let loc = |v: V| locate(&b.graph, v, &src, &nodes);
        let lit = |l: &Lit| lit_cond(l, &loc);
        for (si, s) in p.states.iter().enumerate() {
            if s.owner != Some(bi) || !live[si] {
                continue;
            }
            let ws: Vec<Writer> = plans
                .iter()
                .filter(|(w, _)| *w == si)
                .map(|(_, plan)| Writer { en: es, prefix: es_prefix.clone(), plan, val: &loc, lit: &lit, lit_eg: &lit })
                .collect();
            let name = format!("state {}", s.display_name());
            match shared.state(si) {
                Ref::Bun(x) => cg.bregister(x, &s.binit, &ws, &name)?,
                r => cg.register(r.sig(), s.init, &ws, &name)?,
            }
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
        let each = cg.each;
        // Bundles: everything on the state's wire while running. Constant bundles: a
        // decider outputting the constants while running.
        let direct = comb_ref.get(&si).copied();
        let (kind, reads) = match (s.ty == Ty::Bundle, direct.or(shared.state_sig.get(&si).map(|x| Ref::Op(Operand::Sig(*x)))), shared.state_bun.get(&si)) {
            (true, Some(Ref::Bun(x)), _) => {
                let a = Arith { first: Operand::Sig(each), first_nets: Nets::RED, second: Operand::Sig(run), second_nets: Nets::GREEN, op: ArOp::Mul, out: each };
                (Kind::Arith(a), Some(x))
            }
            (false, Some(Ref::Op(Operand::Const(k))), _) => (arith(Operand::Sig(run), ArOp::Mul, Operand::Const(k), port.sig), None),
            (true, _, Some(&x)) => {
                let a = Arith { first: Operand::Sig(each), first_nets: Nets::RED, second: Operand::Sig(run), second_nets: Nets::GREEN, op: ArOp::Mul, out: each };
                (Kind::Arith(a), Some(x))
            }
            (true, _, None) => {
                let outs = s.binit.iter().map(|(sg, k)| out_const(*sg, *k)).collect();
                (dec(vec![green(c(run, CmpOp::Ne, 0))], outs), None)
            }
            (false, Some(Ref::Op(Operand::Sig(x))), _) => (arith(Operand::Sig(x), ArOp::Mul, Operand::Sig(run), port.sig), None),
            (_, Some(_), _) => unreachable!("output of the wrong kind"),
            (false, None, _) => (arith(Operand::Sig(run), ArOp::Mul, Operand::Const(s.init), port.sig), None),
        };
        let id = cg.net.add(kind, Role::OutputPort { name: port.name.clone(), signal: port.sig });
        let sends = if s.ty == Ty::Bundle { "its bundle".to_string() } else { t.name(port.sig).to_string() };
        let e = &mut cg.net.entities[id];
        e.dir = Dir::East;
        e.description = Some(format!(
            "Ticky output `{}` ({}){}: sends {sends} on wires connected to this combinator's output (right) side.",
            port.name,
            port.ty.name(),
            port.label.as_ref().map(|l| format!(" \"{l}\"")).unwrap_or_default(),
        ));
        cg.nets[0].members.push((id, Conn::InGreen));
        if let Some(x) = reads {
            cg.bread(x, id, false);
        }
        port_ents[pi] = id;
    }
    cg.bfinish();

    Ok(Codegen { netlist: cg.net, nets: cg.nets, port_ents, run_switch, blocks, main, signals_used: cg.used })
}

/// A block that runs every tick: logic is a balanced pipeline reading inputs directly.
/// Returns where each combinational output (`comb`) of the block can be read.
#[allow(clippy::too_many_arguments)]
fn pipelined_block(
    cg: &mut Cg,
    p: &Program,
    bi: usize,
    b: &crate::program::Block,
    pipe: &crate::pipeline::Pipe,
    shared: &Shared,
    live: &[bool],
    comb: &std::collections::HashSet<usize>,
) -> Result<(HashMap<usize, Ref>, u32), Diag> {
    let what = format!("block {}", bi + 1);
    let g = &b.graph;
    let tau = |v: V| pipe.tau[v as usize];
    let owned: Vec<usize> = (0..p.states.len()).filter(|&si| p.states[si].owner == Some(bi) && live[si]).collect();
    let registers = owned.iter().any(|si| !comb.contains(si));
    // Commit only once the pipeline holds values computed from inputs read after the start.
    let (en, en_prefix) = if registers {
        let en = cg.warm(pipe.latency as usize + 1)?;
        (en, if pipe.latency == 0 { cg.rp } else { cg.warm(pipe.latency as usize)? })
    } else {
        (cg.rp, cg.rp)
    };
    let src_ref: Vec<Ref> = b.srcs.iter().map(|k| shared.raw(p, *k).0).collect();

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
    let mut node_ref: HashMap<V, Ref> = HashMap::new();
    for &v in &nodes {
        match g.op(v) {
            Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) | Op::Sel(_) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_) => {
                node_ref.insert(v, Ref::Op(Operand::Sig(cg.alloc()?)));
            }
            Op::BConst(_) | Op::Bun(_) | Op::BMux { .. } | Op::BSelect(..) => {
                node_ref.insert(v, Ref::Bun(cg.bnew()));
            }
            _ => {}
        }
    }
    let mut delayed: HashMap<(V, i32), Ref> = HashMap::new();
    // The value of `u` for the current iteration, on the wire at offset `at`.
    let mut at_ref = |cg: &mut Cg, u: V, at: i32| -> Result<Ref, Diag> {
        let base = match *g.op(u) {
            Op::Const(k) => return Ok(Ref::Op(Operand::Const(k))),
            Op::BConst(_) => return Ok(node_ref[&u]), // constant: no timing
            Op::Src(s) => src_ref[s as usize],
            _ => node_ref[&u],
        };
        let t = tau(u).expect("timed node");
        assert!(t <= at, "pipeline schedule: value needed before it exists");
        let mut cur = base;
        for d in 1..=(at - t) {
            cur = match delayed.get(&(u, t + d)) {
                Some(r) => *r,
                None => {
                    let r = match cur {
                        Ref::Bun(prev) => {
                            let next = cg.bnew();
                            let each = cg.each;
                            let id = cg.loose(arith(Operand::Sig(each), ArOp::Add, Operand::Const(0), each), format!("{what}: delay"));
                            cg.bread(prev, id, false);
                            cg.bprod(next, id);
                            Ref::Bun(next)
                        }
                        r => {
                            let s = cg.alloc()?;
                            cg.core(arith(r.op(), ArOp::Add, Operand::Const(0), s), format!("{what}: delay"));
                            Ref::Op(Operand::Sig(s))
                        }
                    };
                    delayed.insert((u, t + d), r);
                    r
                }
            };
        }
        Ok(cur)
    };
    let as_sig = |o: Operand| match o {
        Operand::Sig(s) => s,
        Operand::Const(_) => unreachable!("constant where a signal is required"),
    };
    for &v in &nodes {
        let Some(&out_ref) = node_ref.get(&v) else { continue };
        if matches!(g.op(v), Op::BConst(_)) {
            cg.emit_bundle(g, v, out_ref.bun(), &|_| unreachable!(), &what);
            continue;
        }
        let t = tau(v).unwrap() - 1;
        if let Op::Bun(_) | Op::BMux { .. } | Op::BSelect(..) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_) = g.op(v) {
            // Operands as of this node's input tick, then the combinators.
            let mut ops: HashMap<V, Ref> = HashMap::new();
            for u in g.operands(v) {
                let r = at_ref(cg, u, t)?;
                ops.insert(u, r);
            }
            let look = |u: V| ops[&u];
            match out_ref {
                Ref::Bun(o) => cg.emit_bundle(g, v, o, &look, &what),
                r => cg.emit_from_bundle(g, v, r.sig(), &look, &what),
            }
            continue;
        }
        let out = out_ref.sig();
        match g.op(v).clone() {
            Op::Ar(op, a, bb) => {
                let (x, y) = (at_ref(cg, a, t)?.op(), at_ref(cg, bb, t)?.op());
                cg.core(arith(x, op, y, out), format!("{what}: arithmetic"));
            }
            Op::Cmp(op, a, bb) => {
                let (x, y) = (as_sig(at_ref(cg, a, t)?.op()), at_ref(cg, bb, t)?.op());
                cg.core(dec_const(vec![Cond { second: y, ..c(x, op, 0) }], out, 1), format!("{what}: comparison"));
            }
            Op::Mux { .. } | Op::Sel(_) => {
                let arms: Vec<(V, V)> = match g.op(v) {
                    Op::Mux { t, f, a, b } => vec![(*t, *a), (*f, *b)],
                    Op::Sel(arms) => arms.clone(),
                    _ => unreachable!(),
                };
                for (cond, val) in arms {
                    let cs = as_sig(at_ref(cg, cond, t)?.op());
                    match at_ref(cg, val, t)?.op() {
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
                            let (x, y) = (as_sig(at_ref(cg, l.a, t)?.op()), at_ref(cg, l.b, t)?.op());
                            conds.push(Cond { second: y, ..c(x, l.op, 0) });
                        }
                        terms.push(conds);
                    }
                    cg.core(dec_const(distribute(&[], &terms), out, k), format!("{what}: condition"));
                }
            }
            _ => unreachable!("not a scalar operation"),
        }
    }

    // Loads read values at offset 0; enable deciders read their conditions one tick early.
    let mut ready: HashMap<(V, i32), Ref> = HashMap::new();
    for (_, plan) in &plans {
        for l in &plan.loads {
            let guard_at = if l.direct || is_true(&l.guard) { 0 } else { -1 };
            for v in crate::ir::dnf_operands(&l.guard) {
                ready.insert((v, guard_at), Ref::Op(at_ref(cg, v, guard_at)?.op()));
            }
            if let LoadVal::Node(v) = l.val {
                ready.insert((v, 0), at_ref(cg, v, 0)?);
            }
        }
        if let Some(k) = &plan.keep {
            for v in crate::ir::dnf_operands(k) {
                ready.insert((v, 0), Ref::Op(at_ref(cg, v, 0)?.op()));
            }
        }
    }
    let mut acc_w: Vec<(usize, Operand)> = Vec::new();
    for (si, a) in &accs {
        acc_w.push((*si, at_ref(cg, a.w, -1)?.op()));
        for v in acc_conds(a) {
            ready.insert((v, 0), Ref::Op(at_ref(cg, v, 0)?.op()));
        }
    }
    // Combinational outputs: the value at offset 0, or one tick later when other states of
    // the block go through registers (whose outputs show values a tick later), so that all
    // outputs of an iteration change together.
    // Conditions checked on the commit tick (direct loads) also push outputs a tick later.
    let late = registers || plans.iter().any(|(si, p)| comb.contains(si) && p.loads.iter().any(|l| l.direct));
    let o = if late { 1 } else { 0 };
    let mut direct: HashMap<usize, Ref> = HashMap::new();
    for (si, plan) in &plans {
        if !comb.contains(si) {
            continue;
        }
        let r = match (plan.loads.as_slice(), plan.loads.first().map(|l| is_true(&l.guard))) {
            ([l], Some(true)) => match l.val {
                LoadVal::Const(k) => Ref::Op(Operand::Const(k)),
                LoadVal::Node(v) => at_ref(cg, v, o)?,
            },
            _ => {
                // Constants under (mutually exclusive) conditions: one decider each.
                let out = cg.alloc()?;
                for l in &plan.loads {
                    let LoadVal::Const(k) = l.val else { unreachable!("checked by combinational()") };
                    if k == 0 {
                        continue;
                    }
                    let mut terms: CDnf = Vec::new();
                    for term in &l.guard {
                        let mut conds = Vec::new();
                        for lit in term {
                            let (x, y) = (at_ref(cg, lit.a, o - 1)?.sig(), at_ref(cg, lit.b, o - 1)?.op());
                            conds.push(Cond { second: y, ..c(x, lit.op, 0) });
                        }
                        terms.push(conds);
                    }
                    cg.core(dec_const(distribute(&[], &terms), out, k), format!("{what}: {}", p.states[*si].display_name()));
                }
                Ref::Op(Operand::Sig(out))
            }
        };
        direct.insert(*si, r);
    }
    let val = |v: V| ready[&(v, 0)];
    let lit_at = |l: &Lit, when: i32| Cond { second: ready[&(l.b, when)].op(), ..c(ready[&(l.a, when)].sig(), l.op, 0) };
    let lit = |l: &Lit| lit_at(l, 0);
    let lit_eg = |l: &Lit| lit_at(l, -1);
    for (si, s) in p.states.iter().enumerate() {
        if s.owner != Some(bi) || !live[si] {
            continue;
        }
        if comb.contains(&si) {
            continue;
        }
        let name = format!("state {}", s.display_name());
        if let Some((_, w)) = acc_w.iter().find(|(a, _)| *a == si) {
            let acc = &accs.iter().find(|(a, _)| *a == si).unwrap().1;
            accumulator(cg, shared.state_sig[&si], s.init, *w, acc, en, &lit, &name);
            continue;
        }
        let ws: Vec<Writer> = plans
            .iter()
            .filter(|(w, _)| *w == si)
            .map(|(_, plan)| Writer { en, prefix: vec![c(en_prefix, CmpOp::Ne, 0)], plan, val: &val, lit: &lit, lit_eg: &lit_eg })
            .collect();
        match shared.state(si) {
            Ref::Bun(x) => cg.bregister(x, &s.binit, &ws, &name)?,
            r => cg.register(r.sig(), s.init, &ws, &name)?,
        }
    }
    Ok((direct, if registers { 1 } else { o as u32 }))
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
    let mut src_ref: Vec<Ref> = Vec::new();
    for &kind in &m.srcs {
        let (raw, name) = shared.raw(p, kind);
        src_ref.push(match kind {
            SrcKind::Input(_) | SrcKind::Foreign(_) | SrcKind::Ticks => cg.sample_ref(raw, any, &format!("main: {name}"))?,
            _ => raw,
        });
    }
    let src = |s: u32| src_ref[s as usize];
    let mut steps = m.steps.clone();
    for s in &mut steps {
        s.plans.retain(|(si, _)| live[*si]);
    }
    let roots: Vec<V> = steps.iter().flat_map(|s| s.roots()).collect();
    let nodes = cg.logic(g, &roots, &src, "main")?;
    let loc = |v: V| locate(g, v, &src, &nodes);
    let opnd = |v: V| loc(v).op();
    let sig_of = |v: V| loc(v).sig();
    let lit = |l: &Lit| lit_cond(l, &loc);
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
                    ws.push(Writer { en: *cms, prefix: prefix.clone(), plan, val: &loc, lit: &lit, lit_eg: &lit });
                }
            }
        }
        let name = format!("variable {}", s.display_name());
        match shared.state(si) {
            Ref::Bun(x) => cg.bregister(x, &s.binit, &ws, &name)?,
            r => cg.register(r.sig(), s.init, &ws, &name)?,
        }
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
            plans.iter().map(|(en, prefix, plan)| Writer { en: *en, prefix: prefix.clone(), plan, val: &loc, lit: &lit, lit_eg: &lit }).collect();
        cg.register(r, 0, &ws, &format!("main: return address of `{func}`"))?;
    }
    Ok(MainStats { steps: stats, combinators: cg.combinators_since(first_ent) })
}
