//! Bundle values: their wires ([`BVal`]), and the combinators for bundle-valued nodes
//! ([`Cg::emit_bundle`]: constants, `Bun` terms incl. lookups, filters, folds and shifts,
//! bundle selects) and for reading a number out of a bundle ([`Cg::emit_from_bundle`]).

use ticky_factorio::*;

use super::*;
use crate::ir::{BOp, BTerm, FOut, Graph, Op, V};

/// The wires of one bundle value. Consumers read it on red (or green, for the second
/// bundle of an element-wise operation); the wire of each colour is made when first needed.
#[derive(Default)]
pub(super) struct BVal {
    /// Producing entities; `true` for constant combinators (single-sided).
    prods: Vec<(EntId, bool)>,
    red: Option<usize>,
    green: Option<usize>,
}

impl Cg {
    pub(super) fn bnew(&mut self) -> BRef {
        self.bvals.push(BVal::default());
        self.bvals.len() - 1
    }

    pub(super) fn bprod(&mut self, r: BRef, e: EntId) {
        let konst = matches!(self.net.entities[e].kind, Kind::Constant(_));
        self.bvals[r].prods.push((e, konst));
    }

    /// Connects `e`'s red (or green) input to bundle `r`.
    pub(super) fn bread(&mut self, r: BRef, e: EntId, on_green: bool) {
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

    /// Connects single-sided entity `e` (a lamp) to bundle `r`'s red wire.
    pub(super) fn bread_single(&mut self, r: BRef, e: EntId) {
        self.bread(r, e, false);
        let ni = self.bvals[r].red.unwrap();
        self.nets[ni].members.last_mut().unwrap().1 = Conn::Red;
    }

    /// Wires every bundle's producers to the bundle's wires.
    pub(super) fn bfinish(&mut self) {
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

    /// Combinators for a bundle-valued node, producing bundle `out`. `r` locates operands.
    /// `direct(x)`: for a one-signal read `x` used only here, the bundle and signal to read
    /// straight from the bundle's wire (no separate read).
    /// `written(x)`: `x` writes its `One` signal onto this bundle's wire itself.
    pub(super) fn emit_bundle(&mut self, g: &Graph, v: V, out: BRef, r: &dyn Fn(V) -> Ref, direct: &dyn Fn(V) -> Option<(V, Sig)>, written: &dyn Fn(V) -> bool, what: &str) {
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
                        BTerm::Set(b, sig, x) => {
                            let (o, n) = scal(x);
                            let a = Arith { first: o, first_nets: n, second: Operand::Sig(sig), second_nets: Nets::RED, op: ArOp::Sub, out: sig };
                            (Kind::Arith(a), vec![(b, false)], matches!(o, Operand::Sig(_)), "set one signal")
                        }
                        BTerm::One(_, x) if written(x) => continue,
                        BTerm::One(sig, x) => match direct(x) {
                            Some((b, s)) => (arith(Operand::Sig(s), ArOp::Add, Operand::Const(0), sig), vec![(b, false)], false, "one signal"),
                            None => (arith(r(x).op(), ArOp::Add, Operand::Const(0), sig), vec![], true, "one signal"),
                        },
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
                        BTerm::Ar(op, a, b, sig) => {
                            let ((x, xn), (y, yn)) = (scal(a), scal(b));
                            (Kind::Arith(Arith { first: x, first_nets: xn, second: y, second_nets: yn, op, out: sig }), vec![], true, "arithmetic")
                        }
                        BTerm::Dec(arms) => {
                            for (d, vals) in arms {
                                if vals.is_empty() {
                                    continue;
                                }
                                let terms: CDnf = d
                                    .iter()
                                    .map(|t| t.iter().map(|l| green(Cond { second: r(l.b).op(), ..cnd(r(l.a).sig(), l.op) })).collect())
                                    .collect();
                                let outs = vals.iter().map(|(s, k)| out_const(*s, *k)).collect();
                                let id = self.loose(dec(distribute(&[], &terms), outs), format!("{what}: condition"));
                                self.on_bus_in(id);
                                self.bprod(out, id);
                            }
                            continue;
                        }
                        BTerm::Shift(sig, x, c) => match direct(x) {
                            Some((b, s)) => (arith(Operand::Sig(s), ArOp::Add, Operand::Const(c), sig), vec![(b, false)], false, "index"),
                            None => (arith(r(x).op(), ArOp::Add, Operand::Const(c), sig), vec![], true, "index"),
                        },
                        BTerm::Hot(t, ix, c) => {
                            let idx = SignalTable::base().index_signal();
                            let cond = Cond {
                                first: each,
                                first_nets: Nets::RED,
                                second: Operand::Sig(idx),
                                second_nets: Nets::GREEN,
                                cmp: CmpOp::Eq,
                                and: true,
                            };
                            (dec(vec![cond], vec![out_const(each, c)]), vec![(t, false), (ix, true)], false, "one-hot")
                        }
                        BTerm::Fold(b, op, c, sig) => {
                            let a = Arith { first: Operand::Sig(each), first_nets: Nets::RED, second: Operand::Const(c), second_nets: Nets::BOTH, op, out: sig };
                            (Kind::Arith(a), vec![(b, false)], false, "to one signal")
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
            Op::BDec(ref arms) => {
                for (d, x) in arms {
                    // The guard reads the bus (green); the bundle comes in on red.
                    let terms: CDnf = d
                        .iter()
                        .map(|t| t.iter().map(|l| green(Cond { second: r(l.b).op(), ..cnd(r(l.a).sig(), l.op) })).collect())
                        .collect();
                    let conds = distribute(&[], &terms);
                    let id = match g.as_bconst(*x) {
                        Some(vals) => {
                            let outs = vals.iter().map(|(s, k)| out_const(*s, *k)).collect();
                            self.loose(dec(conds, outs), format!("{what}: select"))
                        }
                        None => {
                            let o = DOut { sig: self.everything, copy: true, constant: 1, nets: Nets::RED };
                            let id = self.loose(dec(conds, vec![o]), format!("{what}: select"));
                            let rb = r(*x).bun();
                            self.bread(rb, id, false);
                            id
                        }
                    };
                    self.on_bus_in(id);
                    self.bprod(out, id);
                }
            }
            Op::BSelect(b, max, index) => {
                let label = match (max, index) {
                    (true, 0) => "largest".to_string(),
                    (false, 0) => "smallest".to_string(),
                    (true, k) => format!("rank {k} from the largest"),
                    (false, k) => format!("rank {k} from the smallest"),
                };
                let id = self.loose(Kind::Selector(Selector::Select { max, index: index as i32 }), format!("{what}: {label}"));
                let rb = r(b).bun();
                self.bread(rb, id, false);
                self.bprod(out, id);
            }
            Op::BSelectAt(b, max, ix) => {
                // The rank comes from the index signal on its own wire (green); the selector
                // reads both wires, and the index signal takes no part in the ranking.
                let index = SignalTable::base().index_signal();
                let label = if max { "rank k from the largest" } else { "rank k from the smallest" };
                let id = self.loose(Kind::Selector(Selector::SelectAt { max, index }), format!("{what}: {label}"));
                let (rb, ri) = (r(b).bun(), r(ix).bun());
                self.bread(rb, id, false);
                self.bread(ri, id, true);
                self.bprod(out, id);
            }
            Op::BSel(b, ref mode, _) => {
                let label = match mode {
                    Selector::StackSize => "stack sizes".to_string(),
                    Selector::RocketCapacity => "rocket capacities".to_string(),
                    Selector::QualityFilter { cmp, q } => format!("quality {} {}", cmp.symbol(), ticky_factorio::QUALITIES[*q as usize]),
                    Selector::QualitySet { q } => format!("to quality {}", ticky_factorio::QUALITIES[*q as usize]),
                    Selector::Random { .. } => "random pick".to_string(),
                    _ => unreachable!("select and count have their own nodes"),
                };
                let id = self.loose(Kind::Selector(mode.clone()), format!("{what}: {label}"));
                let rb = r(b).bun();
                self.bread(rb, id, false);
                self.bprod(out, id);
            }
            _ => unreachable!("not a bundle node"),
        }
    }

    /// Combinators for a scalar read from a bundle (`b[s]`, totals, counts), onto the bus.
    /// Reads a value out of a bundle onto `out`, times `scale` (1, or a wire sum's factor).
    /// With `out_net`, the result goes on that red net (a cluster's private wire) instead of
    /// the bus.
    pub(super) fn emit_from_bundle(&mut self, g: &Graph, v: V, out: Sig, scale: i32, out_net: Option<usize>, r: &dyn Fn(V) -> Ref, what: &str) {
        let each = self.each;
        if let Op::AGet(b, ix) = *g.op(v) {
            // `each` iterates the positions and the index (green); the index matches itself
            // too, but the array (red) never has the index signal.
            let idx = SignalTable::base().index_signal();
            let cond = Cond { first: each, first_nets: Nets::GREEN, second: Operand::Sig(idx), second_nets: Nets::GREEN, cmp: CmpOp::Eq, and: true };
            let o = DOut { sig: out, copy: true, constant: 1, nets: Nets::RED };
            let id = self.loose(dec(vec![cond], vec![o]), format!("{what}: array read"));
            let (rb, ri) = (r(b).bun(), r(ix).bun());
            self.bread(rb, id, false);
            self.bread(ri, id, true);
            self.nets[0].members.push((id, Conn::OutGreen));
            return;
        }
        if let Op::BDot(a, b) = *g.op(v) {
            // `each(a) * each(b)`, summed onto one signal: with `b` one-hot, a's value there.
            let ar = Arith { first: Operand::Sig(each), first_nets: Nets::RED, second: Operand::Sig(each), second_nets: Nets::GREEN, op: ArOp::Mul, out };
            let id = self.loose(Kind::Arith(ar), format!("{what}: read a signal's value"));
            let (ra, rb) = (r(a).bun(), r(b).bun());
            self.bread(ra, id, false);
            self.bread(rb, id, true);
            self.nets[0].members.push((id, Conn::OutGreen));
            return;
        }
        let copy = |x: Sig| if scale == 1 { arith(Operand::Sig(x), ArOp::Add, Operand::Const(0), out) } else { arith(Operand::Sig(x), ArOp::Mul, Operand::Const(scale), out) };
        let (kind, b, label) = match *g.op(v) {
            Op::BGet(b, s) => (copy(s), b, "read one signal"),
            Op::BTotal(b) => (copy(each), b, "total"),
            Op::BCount(b) => (dec_const(vec![cnd(each, CmpOp::Ne)], out, scale), b, "count"),
            _ => unreachable!("not a bundle read"),
        };
        // Only the bundle is wired to the input, so reading both colours is fine.
        let id = self.loose(kind, format!("{what}: {label}"));
        let rb = r(b).bun();
        self.bread(rb, id, false);
        match out_net {
            Some(n) => self.nets[n].members.push((id, Conn::OutRed)),
            None => self.nets[0].members.push((id, Conn::OutGreen)),
        }
    }
}
