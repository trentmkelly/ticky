//! Tick-exact simulator for a [`Netlist`]: the same entities and wires that go into the
//! blueprint. Each tick, every wire network carries the sum of everything connected to it,
//! and every combinator computes its next output from the networks on its input side,
//! so an output becomes visible one tick after its inputs, as in Factorio.

use std::collections::HashMap;

use ticky_factorio::{items, Conn, Cond, EntId, Kind, Netlist, Nets, Operand, Selector, Sig, SignalKind, SignalTable};

/// Values on one wire network, stored densely with a list of touched signals.
#[derive(Clone)]
struct NetValues {
    dense: Vec<i32>,
    touched: Vec<u16>,
}

impl NetValues {
    fn new(n: usize) -> Self {
        NetValues { dense: vec![0; n], touched: Vec::new() }
    }

    fn add(&mut self, s: Sig, v: i32) {
        if s.0 as usize >= self.dense.len() {
            // A signal interned after the simulator was built (e.g. named by a test).
            self.dense.resize(s.0 as usize + 1, 0);
        }
        let slot = &mut self.dense[s.0 as usize];
        if *slot == 0 && v != 0 {
            self.touched.push(s.0);
        }
        *slot = slot.wrapping_add(v);
    }

    fn get(&self, s: Sig) -> i32 {
        self.dense.get(s.0 as usize).copied().unwrap_or(0)
    }

    fn clear(&mut self) {
        for &s in &self.touched {
            self.dense[s as usize] = 0;
        }
        self.touched.clear();
    }
}

const CONNS: [Conn; 6] = [Conn::InRed, Conn::InGreen, Conn::OutRed, Conn::OutGreen, Conn::Red, Conn::Green];

fn conn_index(c: Conn) -> usize {
    CONNS.iter().position(|x| *x == c).expect("circuit connector")
}

pub struct Sim<'a> {
    pub netlist: &'a Netlist,
    /// Net index for each (entity, connector).
    conn_net: Vec<[usize; 6]>,
    nets: Vec<NetValues>,
    /// Current output of each entity (combinators only).
    outputs: Vec<Vec<(Sig, i32)>>,
    /// Signals injected into an entity's input side, standing in for the player's wires.
    external: HashMap<EntId, Vec<(Sig, i32)>>,
    /// Constant combinator on/off switches.
    const_on: Vec<bool>,
    /// The wildcard signals: each, everything, anything.
    each: Sig,
    everything: Sig,
    anything: Sig,
    /// The random selectors' current picks.
    picks: HashMap<EntId, Option<Sig>>,
    /// Seed for the random selectors (the game's picks can't be reproduced; tests on random
    /// values check ranges).
    pub seed: u64,
    pub tick: u64,
}

fn find(parent: &mut [usize], mut x: usize) -> usize {
    while parent[x] != x {
        parent[x] = parent[parent[x]];
        x = parent[x];
    }
    x
}

impl<'a> Sim<'a> {
    pub fn new(netlist: &'a Netlist) -> Self {
        let n = netlist.entities.len();
        let node = |e: EntId, c: Conn| e * 6 + conn_index(c);
        let mut parent: Vec<usize> = (0..n * 6).collect();
        for w in &netlist.wires {
            if w.a.1 == Conn::Copper {
                continue;
            }
            let (a, b) = (find(&mut parent, node(w.a.0, w.a.1)), find(&mut parent, node(w.b.0, w.b.1)));
            parent[a] = b;
        }
        let mut ids = HashMap::new();
        let mut conn_net = vec![[0usize; 6]; n];
        for (e, slots) in conn_net.iter_mut().enumerate() {
            for (ci, c) in CONNS.iter().enumerate() {
                let root = find(&mut parent, node(e, *c));
                let next = ids.len();
                slots[ci] = *ids.entry(root).or_insert(next);
            }
        }
        let t = SignalTable::base();
        let nsig = t.len();
        let const_on = netlist
            .entities
            .iter()
            .map(|e| matches!(&e.kind, Kind::Constant(c) if c.on))
            .collect();
        Sim {
            netlist,
            conn_net,
            nets: vec![NetValues::new(nsig); ids.len()],
            outputs: vec![Vec::new(); n],
            external: HashMap::new(),
            const_on,
            each: t.special("signal-each"),
            everything: t.special("signal-everything"),
            anything: t.special("signal-anything"),
            picks: HashMap::new(),
            seed: 0x7469636b79,
            tick: 0,
        }
    }

    fn net(&self, e: EntId, c: Conn) -> usize {
        self.conn_net[e][conn_index(c)]
    }

    /// Sets the signals the outside world feeds into `e`'s input (replaces previous values).
    pub fn set_external(&mut self, e: EntId, values: Vec<(Sig, i32)>) {
        self.external.insert(e, values);
    }

    pub fn set_constant_on(&mut self, e: EntId, on: bool) {
        self.const_on[e] = on;
    }

    /// The value of `s` in entity `e`'s own output.
    pub fn output_of(&self, e: EntId, s: Sig) -> i32 {
        self.outputs[e].iter().filter(|(x, _)| *x == s).map(|(_, v)| *v).sum()
    }

    /// Everything in entity `e`'s own output (nonzero signals).
    pub fn outputs_of(&self, e: EntId) -> &[(Sig, i32)] {
        &self.outputs[e]
    }

    /// The value of `s` on the network attached to `e`'s connector `c` (as of the last tick).
    pub fn net_value(&self, e: EntId, c: Conn, s: Sig) -> i32 {
        self.nets[self.net(e, c)].get(s)
    }

    fn read(&self, e: EntId, s: Sig, nets: Nets) -> i32 {
        let mut v = 0i32;
        if nets.red {
            v = v.wrapping_add(self.nets[self.net(e, Conn::InRed)].get(s));
        }
        if nets.green {
            v = v.wrapping_add(self.nets[self.net(e, Conn::InGreen)].get(s));
        }
        v
    }

    /// Nonzero signals on the selected input networks of `e`, in signal order.
    fn signals(&self, e: EntId, nets: Nets) -> Vec<(Sig, i32)> {
        let mut ids: Vec<u16> = Vec::new();
        if nets.red {
            ids.extend(&self.nets[self.net(e, Conn::InRed)].touched);
        }
        if nets.green {
            ids.extend(&self.nets[self.net(e, Conn::InGreen)].touched);
        }
        ids.sort_unstable();
        ids.dedup();
        ids.into_iter().map(|i| (Sig(i), self.read(e, Sig(i), nets))).filter(|(_, v)| *v != 0).collect()
    }

    fn is_each(&self, o: Operand) -> bool {
        o == Operand::Sig(self.each)
    }

    /// Signals an `each` decider iterates: those on the networks of every `each` operand.
    fn each_domain(&self, e: EntId, conds: &[Cond]) -> Vec<Sig> {
        let mut out: Vec<Sig> = Vec::new();
        for c in conds {
            if c.first == self.each {
                out.extend(self.signals(e, c.first_nets).into_iter().map(|(s, _)| s));
            }
            if self.is_each(c.second) {
                out.extend(self.signals(e, c.second_nets).into_iter().map(|(s, _)| s));
            }
        }
        out.sort_unstable();
        out.dedup();
        out
    }

    /// Evaluates decider conditions (OR of AND-groups), with `each` standing for `cur`.
    fn conds_hold(&self, e: EntId, conds: &[Cond], cur: Option<Sig>) -> bool {
        let mut any = false;
        let mut group = true;
        for (i, c) in conds.iter().enumerate() {
            if i > 0 && !c.and {
                any |= group;
                group = true;
            }
            let y = match c.second {
                Operand::Sig(s) if s == self.each => self.read(e, cur.expect("each outside an each decider"), c.second_nets),
                o => self.operand(e, o, c.second_nets),
            };
            let ok = if c.first == self.everything {
                self.signals(e, c.first_nets).iter().all(|(_, x)| c.cmp.apply(*x, y))
            } else if c.first == self.anything {
                self.signals(e, c.first_nets).iter().any(|(_, x)| c.cmp.apply(*x, y))
            } else if c.first == self.each {
                c.cmp.apply(self.read(e, cur.expect("each outside an each decider"), c.first_nets), y)
            } else {
                c.cmp.apply(self.read(e, c.first, c.first_nets), y)
            };
            group &= ok;
        }
        any || (group && !conds.is_empty())
    }

    fn operand(&self, e: EntId, o: Operand, nets: Nets) -> i32 {
        match o {
            Operand::Sig(s) => self.read(e, s, nets),
            Operand::Const(c) => c,
        }
    }

    /// Advances one game tick.
    pub fn step(&mut self) {
        for n in &mut self.nets {
            n.clear();
        }
        for (e, ent) in self.netlist.entities.iter().enumerate() {
            match &ent.kind {
                Kind::Arith(_) | Kind::Decider(_) | Kind::Selector(_) => {
                    let (r, g) = (self.net(e, Conn::OutRed), self.net(e, Conn::OutGreen));
                    for &(s, v) in &self.outputs[e] {
                        self.nets[r].add(s, v);
                        self.nets[g].add(s, v);
                    }
                }
                Kind::Constant(c) if self.const_on[e] => {
                    let (r, g) = (self.net(e, Conn::Red), self.net(e, Conn::Green));
                    for &(s, v) in &c.values {
                        self.nets[r].add(s, v);
                        if g != r {
                            self.nets[g].add(s, v);
                        }
                    }
                }
                _ => {}
            }
        }
        for (&e, vals) in &self.external {
            let r = self.net(e, Conn::InRed);
            for &(s, v) in vals {
                self.nets[r].add(s, v);
            }
        }
        for (e, ent) in self.netlist.entities.iter().enumerate() {
            let out = match &ent.kind {
                Kind::Arith(a) => {
                    let (fe, se) = (self.is_each(a.first), self.is_each(a.second));
                    if fe || se {
                        // Each: the operation applies to every signal on the `each` operands'
                        // networks; the result is per signal, or summed into one output.
                        let mut dom: Vec<Sig> = Vec::new();
                        if fe {
                            dom.extend(self.signals(e, a.first_nets).into_iter().map(|(s, _)| s));
                        }
                        if se {
                            dom.extend(self.signals(e, a.second_nets).into_iter().map(|(s, _)| s));
                        }
                        dom.sort_unstable();
                        dom.dedup();
                        let mut per = Vec::new();
                        let mut total = 0i32;
                        for s in dom {
                            let x = if fe { self.read(e, s, a.first_nets) } else { self.operand(e, a.first, a.first_nets) };
                            let y = if se { self.read(e, s, a.second_nets) } else { self.operand(e, a.second, a.second_nets) };
                            let v = a.op.apply(x, y);
                            if a.out == self.each {
                                if v != 0 {
                                    per.push((s, v));
                                }
                            } else {
                                total = total.wrapping_add(v);
                            }
                        }
                        if a.out != self.each && total != 0 {
                            per.push((a.out, total));
                        }
                        per
                    } else {
                        let x = self.operand(e, a.first, a.first_nets);
                        let y = self.operand(e, a.second, a.second_nets);
                        let v = a.op.apply(x, y);
                        if v == 0 {
                            vec![]
                        } else {
                            vec![(a.out, v)]
                        }
                    }
                }
                Kind::Decider(d) => {
                    let uses_each = d.conds.iter().any(|c| c.first == self.each || self.is_each(c.second));
                    let mut out: Vec<(Sig, i32)> = Vec::new();
                    if uses_each {
                        let passing: Vec<Sig> =
                            self.each_domain(e, &d.conds).into_iter().filter(|s| self.conds_hold(e, &d.conds, Some(*s))).collect();
                        for o in &d.outputs {
                            if o.sig == self.each {
                                for &s in &passing {
                                    out.push((s, if o.copy { self.read(e, s, o.nets) } else { o.constant }));
                                }
                            } else {
                                // A single output sums over the passing signals.
                                let mut v = 0i32;
                                for &s in &passing {
                                    v = v.wrapping_add(if o.copy { self.read(e, s, o.nets) } else { o.constant });
                                }
                                out.push((o.sig, v));
                            }
                        }
                    } else if self.conds_hold(e, &d.conds, None) {
                        for o in &d.outputs {
                            if o.sig == self.everything {
                                for (s, v) in self.signals(e, o.nets) {
                                    out.push((s, if o.copy { v } else { o.constant }));
                                }
                            } else {
                                out.push((o.sig, if o.copy { self.read(e, o.sig, o.nets) } else { o.constant }));
                            }
                        }
                    }
                    // Several outputs may write the same signal: sum them.
                    out.sort_by_key(|(s, _)| *s);
                    let mut merged: Vec<(Sig, i32)> = Vec::new();
                    for (s, v) in out {
                        match merged.last_mut() {
                            Some((ls, lv)) if *ls == s => *lv = lv.wrapping_add(v),
                            _ => merged.push((s, v)),
                        }
                    }
                    merged.retain(|(_, v)| *v != 0);
                    merged
                }
                Kind::Selector(sel) => {
                    let mut ins = self.signals(e, Nets::BOTH);
                    match sel {
                        Selector::Select { .. } | Selector::SelectAt { .. } => {
                            let (max, index) = match sel {
                                Selector::Select { max, index } => (max, *index),
                                Selector::SelectAt { max, index } => {
                                    // The index signal is read, and takes no part in the ranking.
                                    let k = ins.iter().find(|(s, _)| s == index).map_or(0, |x| x.1);
                                    ins.retain(|(s, _)| s != index);
                                    (max, k)
                                }
                                _ => unreachable!(),
                            };
                            // Ties in the game's order (`SignalTable::rank`): min is max reversed.
                            let t = SignalTable::base();
                            if *max {
                                ins.sort_by_key(|(s, v)| (std::cmp::Reverse(*v), t.rank(*s)));
                            } else {
                                ins.sort_by_key(|(s, v)| (*v, std::cmp::Reverse(t.rank(*s))));
                            }
                            usize::try_from(index).ok().and_then(|i| ins.get(i).copied()).into_iter().collect()
                        }
                        Selector::Count { out } => {
                            if ins.is_empty() {
                                vec![]
                            } else {
                                vec![(*out, ins.len() as i32)]
                            }
                        }
                        Selector::StackSize | Selector::RocketCapacity => {
                            let t = SignalTable::base();
                            let mut v: Vec<(Sig, i32)> = ins
                                .iter()
                                .filter(|(s, _)| t.info(*s).kind == SignalKind::Item)
                                .filter_map(|(s, _)| {
                                    let n = &t.info(*s).name;
                                    let k = if matches!(sel, Selector::StackSize) { items::stack_size(n) } else { items::rocket_capacity(n) };
                                    Some((*s, k?))
                                })
                                .collect();
                            v.sort_by_key(|x| x.0);
                            v
                        }
                        Selector::QualityFilter { cmp, q } => {
                            let t = SignalTable::base();
                            ins.retain(|(s, _)| cmp.apply(t.info(*s).quality as i32, *q as i32));
                            ins.sort_by_key(|x| x.0);
                            ins
                        }
                        Selector::QualitySet { q } => {
                            let t = SignalTable::base();
                            let mut m: Vec<(Sig, i32)> = Vec::new();
                            for (s, v) in ins {
                                let s = t.with_quality(s, *q);
                                match m.iter_mut().find(|x| x.0 == s) {
                                    Some(x) => x.1 = x.1.wrapping_add(v),
                                    None => m.push((s, v)),
                                }
                            }
                            m.retain(|x| x.1 != 0);
                            m.sort_by_key(|x| x.0);
                            m
                        }
                        Selector::Random { interval } => {
                            // A new pick every `interval` ticks (every tick for 0 or 1), from
                            // the inputs in the game's signal order; between picks, the picked
                            // signal with its current value.
                            let t = SignalTable::base();
                            ins.sort_by_key(|(s, _)| t.rank(*s));
                            let n = (*interval).max(1) as u64;
                            if self.tick % n == 0 || !self.picks.contains_key(&e) {
                                let mut h = self.seed ^ (e as u64).wrapping_mul(0x9E37_79B9_7F4A_7C15) ^ self.tick.wrapping_mul(0xD1B5_4A32_D192_ED03);
                                h ^= h >> 31;
                                h = h.wrapping_mul(0xBF58_476D_1CE4_E5B9);
                                h ^= h >> 29;
                                let pick = (!ins.is_empty()).then(|| ins[(h % ins.len() as u64) as usize].0);
                                self.picks.insert(e, pick);
                            }
                            match self.picks[&e] {
                                Some(s) => ins.into_iter().filter(|x| x.0 == s).collect(),
                                None => vec![],
                            }
                        }
                    }
                }
                _ => continue,
            };
            self.outputs[e] = out;
        }
        self.tick += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ticky_factorio::*;

    /// A one-combinator clock: x' = (x + 1 < 4) ? x + 1 : 0, fed by a constant 1.
    #[test]
    fn decider_clock() {
        let t = SignalTable::base();
        let x = t.resolve_ident("X").unwrap();
        let mut n = Netlist::default();
        let c = n.add(Kind::Constant(ConstComb { values: vec![(x, 1)], on: true }), Role::Core);
        let d = n.add(
            Kind::Decider(Decider {
                conds: vec![Cond {
                    first: x,
                    first_nets: Nets::BOTH,
                    second: Operand::Const(4),
                    second_nets: Nets::BOTH,
                    cmp: CmpOp::Lt,
                    and: false,
                }],
                outputs: vec![DOut { sig: x, copy: true, constant: 1, nets: Nets::BOTH }],
            }),
            Role::Core,
        );
        n.wire((c, Conn::Green), (d, Conn::InGreen));
        n.wire((d, Conn::OutGreen), (d, Conn::InGreen));
        let mut sim = Sim::new(&n);
        let mut seen = vec![];
        for _ in 0..9 {
            sim.step();
            seen.push(sim.output_of(d, x));
        }
        assert_eq!(seen, vec![1, 2, 3, 0, 1, 2, 3, 0, 1]);
    }
}

/// The wildcard semantics, checked against the in-game probe (harness/ticky-harness/scenarios/probe).
#[cfg(test)]
mod wildcard_tests {
    use super::*;
    use ticky_factorio::*;

    fn sig(n: &str) -> Sig {
        let t = SignalTable::base();
        t.lookup(n).unwrap_or_else(|| t.special(n))
    }

    /// Runs one combinator fed with `red` and `green`; returns its sorted output by name.
    fn probe(kind: Kind, red: &[(&str, i32)], green: &[(&str, i32)]) -> Vec<(String, i32)> {
        let mut n = Netlist::default();
        let c = n.add(kind, Role::Core);
        for (vals, conn) in [(red, Conn::InRed), (green, Conn::InGreen)] {
            if vals.is_empty() {
                continue;
            }
            let k = n.add(
                Kind::Constant(ConstComb { values: vals.iter().map(|(s, v)| (sig(s), *v)).collect(), on: true }),
                Role::Core,
            );
            n.wire((k, if conn == Conn::InRed { Conn::Red } else { Conn::Green }), (c, conn));
        }
        let mut sim = Sim::new(&n);
        sim.step();
        sim.step();
        let t = SignalTable::base();
        let mut out: Vec<(String, i32)> = sim.outputs_of(c).iter().map(|(s, v)| (t.name(*s).to_string(), *v)).collect();
        out.sort();
        out
    }

    const BUNDLE: &[(&str, i32)] = &[("iron-plate", 5), ("copper-plate", -3), ("signal-check", 7), ("signal-A", 100)];
    const SCAL: &[(&str, i32)] = &[("signal-A", 2), ("signal-check", 1)];

    fn s(o: &str) -> Operand {
        Operand::Sig(sig(o))
    }

    fn ar(first: Operand, fnets: Nets, op: ArOp, second: Operand, snets: Nets, out: &str) -> Kind {
        Kind::Arith(Arith { first, first_nets: fnets, second, second_nets: snets, op, out: sig(out) })
    }

    fn cond(first: &str, fnets: Nets, cmp: CmpOp, second: Operand, snets: Nets, and: bool) -> Cond {
        Cond { first: sig(first), first_nets: fnets, second, second_nets: snets, cmp, and }
    }

    fn out(o: &str, copy: bool, constant: i32, nets: Nets) -> DOut {
        DOut { sig: sig(o), copy, constant, nets }
    }

    fn v(pairs: &[(&str, i32)]) -> Vec<(String, i32)> {
        let mut x: Vec<(String, i32)> = pairs.iter().map(|(s, v)| (s.to_string(), *v)).collect();
        x.sort();
        x
    }

    #[test]
    fn matches_the_game() {
        let (r, g, b) = (Nets::RED, Nets::GREEN, Nets::BOTH);
        let k = Operand::Const;
        // P1 each(red) * A(green) -> each
        assert_eq!(
            probe(ar(s("signal-each"), r, ArOp::Mul, s("signal-A"), g, "signal-each"), BUNDLE, SCAL),
            v(&[("copper-plate", -6), ("iron-plate", 10), ("signal-A", 200), ("signal-check", 14)])
        );
        // P2 each(red) > 0 and each(red) < 50 and A(green) = 2 -> each copied from red
        let d = Decider {
            conds: vec![
                cond("signal-each", r, CmpOp::Gt, k(0), b, true),
                cond("signal-each", r, CmpOp::Lt, k(50), b, true),
                cond("signal-A", g, CmpOp::Eq, k(2), b, true),
            ],
            outputs: vec![out("signal-each", true, 1, r)],
        };
        assert_eq!(probe(Kind::Decider(d), BUNDLE, SCAL), v(&[("iron-plate", 5), ("signal-check", 7)]));
        // P3a count, P3b sum of passing values
        let d = Decider { conds: vec![cond("signal-each", r, CmpOp::Ne, k(0), b, true)], outputs: vec![out("signal-X", false, 1, b)] };
        assert_eq!(probe(Kind::Decider(d), BUNDLE, SCAL), v(&[("signal-X", 4)]));
        let d = Decider { conds: vec![cond("signal-each", r, CmpOp::Gt, k(0), b, true)], outputs: vec![out("signal-X", true, 1, r)] };
        assert_eq!(probe(Kind::Decider(d), BUNDLE, SCAL), v(&[("signal-X", 112)]));
        // P4 check(green) != 0 -> everything copied from red
        let d = Decider {
            conds: vec![cond("signal-check", g, CmpOp::Ne, k(0), b, true)],
            outputs: vec![out("signal-everything", true, 1, r)],
        };
        assert_eq!(probe(Kind::Decider(d), BUNDLE, SCAL), v(BUNDLE));
        // P5 each(red) + 0 -> X
        assert_eq!(probe(ar(s("signal-each"), r, ArOp::Add, k(0), b, "signal-X"), BUNDLE, SCAL), v(&[("signal-X", 109)]));
        // P6 selector
        assert_eq!(probe(Kind::Selector(Selector::Select { max: true, index: 0 }), BUNDLE, &[]), v(&[("signal-A", 100)]));
        assert_eq!(probe(Kind::Selector(Selector::Select { max: false, index: 0 }), BUNDLE, &[]), v(&[("copper-plate", -3)]));
        assert_eq!(probe(Kind::Selector(Selector::Count { out: sig("signal-X") }), BUNDLE, &[]), v(&[("signal-X", 4)]));
        // P7 each(red) * each(green)
        assert_eq!(
            probe(ar(s("signal-each"), r, ArOp::Mul, s("signal-each"), g, "signal-each"), BUNDLE, &[("iron-plate", 3), ("signal-A", 2)]),
            v(&[("iron-plate", 15), ("signal-A", 200)])
        );
        // P8 each(red) > 0 -> each = 5
        let d = Decider { conds: vec![cond("signal-each", r, CmpOp::Gt, k(0), b, true)], outputs: vec![out("signal-each", false, 5, b)] };
        assert_eq!(probe(Kind::Decider(d), BUNDLE, SCAL), v(&[("iron-plate", 5), ("signal-A", 5), ("signal-check", 5)]));
        // P9 10 - each(red)
        assert_eq!(
            probe(ar(k(10), b, ArOp::Sub, s("signal-each"), r, "signal-each"), BUNDLE, SCAL),
            v(&[("copper-plate", 13), ("iron-plate", 5), ("signal-A", -90), ("signal-check", 3)])
        );
        // P10 each(red) < A(green)
        let d = Decider {
            conds: vec![cond("signal-each", r, CmpOp::Lt, s("signal-A"), g, true)],
            outputs: vec![out("signal-each", true, 1, r)],
        };
        assert_eq!(probe(Kind::Decider(d), BUNDLE, SCAL), v(&[("copper-plate", -3)]));
        // P12 each(red) + each(green): union
        assert_eq!(
            probe(ar(s("signal-each"), r, ArOp::Add, s("signal-each"), g, "signal-each"), BUNDLE, &[("iron-plate", 3), ("signal-B", 2)]),
            v(&[("copper-plate", -3), ("iron-plate", 8), ("signal-A", 100), ("signal-B", 2), ("signal-check", 7)])
        );
        // P13 each(red) / each(green): 0 where the divisor is missing
        assert_eq!(
            probe(ar(s("signal-each"), r, ArOp::Div, s("signal-each"), g, "signal-each"), BUNDLE, &[("iron-plate", 2), ("signal-B", 2)]),
            v(&[("iron-plate", 2)])
        );
        // P15 everything(red) > -10 -> X = 1
        let d = Decider { conds: vec![cond("signal-everything", r, CmpOp::Gt, k(-10), b, true)], outputs: vec![out("signal-X", false, 1, b)] };
        assert_eq!(probe(Kind::Decider(d), BUNDLE, SCAL), v(&[("signal-X", 1)]));
    }

    /// The level 4 probes (signal arrays), same scenario.
    #[test]
    fn arrays_match_the_game() {
        let (r, g, b) = (Nets::RED, Nets::GREEN, Nets::BOTH);
        let k = Operand::Const;
        let arr: &[(&str, i32)] = &[("iron-plate", 5), ("copper-plate", -3), ("coal", 9)];
        let pos: &[(&str, i32)] = &[("iron-plate", 1), ("copper-plate", 2), ("coal", 3)];
        let pos_i: &[(&str, i32)] = &[("iron-plate", 1), ("copper-plate", 2), ("coal", 3), ("signal-I", 2)];
        // L1 read: each(green) = I(green) -> X copied from red
        let d = Decider { conds: vec![cond("signal-each", g, CmpOp::Eq, s("signal-I"), g, true)], outputs: vec![out("signal-X", true, 1, r)] };
        assert_eq!(probe(Kind::Decider(d), arr, pos_i), v(&[("signal-X", -3)]));
        // L2 one-hot: each(red) = I(green) -> each = 1
        let d = Decider { conds: vec![cond("signal-each", r, CmpOp::Eq, s("signal-I"), g, true)], outputs: vec![out("signal-each", false, 1, b)] };
        assert_eq!(probe(Kind::Decider(d), pos, &[("signal-I", 2)]), v(&[("copper-plate", 1)]));
        // L3 mask: each(red) != 0 and each(green) = 0 -> each copied from red
        let d = Decider {
            conds: vec![cond("signal-each", r, CmpOp::Ne, k(0), b, true), cond("signal-each", g, CmpOp::Eq, k(0), b, true)],
            outputs: vec![out("signal-each", true, 1, r)],
        };
        assert_eq!(probe(Kind::Decider(d), arr, &[("copper-plate", 1)]), v(&[("coal", 9), ("iron-plate", 5)]));
        // L4/L5 each >> 1 -> X: arithmetic shift, summed
        let shr = || ar(s("signal-each"), r, ArOp::Shr, k(1), b, "signal-X");
        assert_eq!(probe(shr(), &[("iron-plate", -5)], &[]), v(&[("signal-X", -3)]));
        // (The game lists `signal-X=0` for the combinator, but a 0 is nothing on the wire.)
        assert_eq!(probe(shr(), &[("iron-plate", 7), ("copper-plate", -5)], &[]), v(&[]));
        // L6/L7 selector ranks (ties: equal values, either signal); L8 out of range
        let ties: &[(&str, i32)] = &[("iron-plate", 3), ("copper-plate", 3), ("coal", 1), ("stone", -7)];
        let sel = |max: bool, index: i32| Kind::Selector(Selector::Select { max, index });
        let value = |o: Vec<(String, i32)>| o.iter().map(|x| x.1).collect::<Vec<_>>();
        for (i, want) in [3, 3, 1, -7].into_iter().enumerate() {
            assert_eq!(value(probe(sel(true, i as i32), ties, &[])), vec![want]);
            assert_eq!(value(probe(sel(false, 3 - i as i32), ties, &[])), vec![want]);
        }
        assert_eq!(probe(sel(true, 0), ties, &[]), v(&[("iron-plate", 3)]));
        assert_eq!(probe(sel(true, 9), ties, &[]), v(&[]));
        // L9 the selector sums both wires
        assert_eq!(probe(sel(true, 0), &[("iron-plate", 3)], &[("iron-plate", 4), ("coal", 5)]), v(&[("iron-plate", 7)]));
    }

    /// A selector reading its rank from a signal (harness/ticky-harness/scenarios/selprobe):
    /// the index signal takes no part in the ranking; missing means 0; past the end, nothing.
    #[test]
    fn selector_index_signal_matches_the_game() {
        let b: &[(&str, i32)] = &[("iron-plate", 100), ("copper-plate", 50), ("coal", 10)];
        let sel = |max: bool| Kind::Selector(Selector::SelectAt { max, index: sig("signal-I") });
        let want_max = [v(&[("iron-plate", 100)]), v(&[("copper-plate", 50)]), v(&[("coal", 10)]), v(&[]), v(&[])];
        let want_min = [v(&[("coal", 10)]), v(&[("copper-plate", 50)]), v(&[("iron-plate", 100)]), v(&[]), v(&[])];
        for i in 0..5 {
            let idx: &[(&str, i32)] = if i == 0 { &[] } else { &[("signal-I", i)] };
            assert_eq!(probe(sel(true), b, idx), want_max[i as usize]);
            assert_eq!(probe(sel(false), b, idx), want_min[i as usize]);
        }
    }

    /// The selector's order among equal values (harness/ticky-harness/scenarios/tieprobe):
    /// items, fluids, virtual signals, each in prototype order, then quality; min reverses it.
    #[test]
    fn selector_ties_match_the_game() {
        let t = SignalTable::base();
        let q = |n: &str, quality: u8| t.with_quality(sig(n), quality);
        let order = |vals: &[(Sig, i32)], max: bool| -> Vec<Sig> {
            (0..vals.len())
                .map(|k| {
                    let mut n = Netlist::default();
                    let c = n.add(Kind::Selector(Selector::Select { max, index: k as i32 }), Role::Core);
                    let kc = n.add(Kind::Constant(ConstComb { values: vals.to_vec(), on: true }), Role::Core);
                    n.wire((kc, Conn::Red), (c, Conn::InRed));
                    let mut sim = Sim::new(&n);
                    sim.step();
                    sim.step();
                    sim.outputs_of(c)[0].0
                })
                .collect()
        };
        let check = |set: &[Sig], want_max: &[Sig]| {
            let vals: Vec<(Sig, i32)> = set.iter().map(|s| (*s, 5)).collect();
            assert_eq!(order(&vals, true), want_max);
            let rev: Vec<Sig> = want_max.iter().rev().copied().collect();
            assert_eq!(order(&vals, false), rev);
        };
        let n = |names: &[&str]| names.iter().map(|x| sig(x)).collect::<Vec<_>>();
        check(&n(&["wood", "iron-plate", "coal", "copper-plate", "stone", "iron-ore"]), &n(&["wood", "coal", "stone", "iron-ore", "iron-plate", "copper-plate"]));
        check(&n(&["signal-Z", "signal-A", "signal-0", "signal-red", "signal-check", "signal-B"]), &n(&["signal-0", "signal-A", "signal-B", "signal-Z", "signal-red", "signal-check"]));
        check(&n(&["water", "coal", "signal-A", "iron-plate", "crude-oil", "signal-dot"]), &n(&["coal", "iron-plate", "water", "crude-oil", "signal-A", "signal-dot"]));
        check(
            &[q("signal-A", 2), q("signal-A", 0), q("signal-B", 1), q("signal-A", 4), q("signal-A", 1), q("coal", 3)],
            &[q("coal", 3), q("signal-A", 0), q("signal-A", 1), q("signal-A", 2), q("signal-A", 4), q("signal-B", 1)],
        );
    }
}

/// The selector modes from the `qprobe` and `itemdump` scenarios (Factorio 2.0.77, Quality mod).
#[cfg(test)]
mod selector_mode_tests {
    use super::*;
    use ticky_factorio::*;

    fn probe(kind: Kind, red: &[(&str, i32)], green: &[(&str, i32)]) -> Vec<String> {
        let t = SignalTable::base();
        let mut n = Netlist::default();
        let c = n.add(kind, Role::Core);
        for (vals, conn) in [(red, Conn::InRed), (green, Conn::InGreen)] {
            if vals.is_empty() {
                continue;
            }
            let values = vals.iter().map(|(s, v)| (t.lookup_display(s).unwrap(), *v)).collect();
            let k = n.add(Kind::Constant(ConstComb { values, on: true }), Role::Core);
            n.wire((k, if conn == Conn::InRed { Conn::Red } else { Conn::Green }), (c, conn));
        }
        let mut sim = Sim::new(&n);
        sim.step();
        sim.step();
        let mut out: Vec<String> = sim.outputs_of(c).iter().map(|(s, v)| format!("{}={v}", t.display(*s))).collect();
        out.sort();
        out
    }

    const B: &[(&str, i32)] = &[("iron-plate", 100), ("copper-plate", 50), ("signal-A", 7), ("water", 9)];
    const MIXED: &[(&str, i32)] =
        &[("iron-plate", 100), ("iron-plate@rare", 3), ("iron-plate@epic", 5), ("signal-A@uncommon", 7), ("signal-B@legendary", 11)];

    #[test]
    fn quality_modes_match_the_game() {
        let set = |q| Kind::Selector(Selector::QualitySet { q });
        assert_eq!(probe(set(4), B, &[]), ["copper-plate@legendary=50", "iron-plate@legendary=100", "signal-A@legendary=7", "water@legendary=9"]);
        assert_eq!(probe(set(2), MIXED, &[]), ["iron-plate@rare=108", "signal-A@rare=7", "signal-B@rare=11"]);
        assert_eq!(probe(set(0), MIXED, &[]), ["iron-plate=108", "signal-A=7", "signal-B=11"]);
        let qf = |cmp| Kind::Selector(Selector::QualityFilter { cmp, q: 2 });
        assert_eq!(probe(qf(CmpOp::Eq), MIXED, B), ["iron-plate@rare=3"]);
        assert_eq!(probe(qf(CmpOp::Gt), MIXED, B), ["iron-plate@epic=5", "signal-B@legendary=11"]);
        assert_eq!(
            probe(qf(CmpOp::Lt), MIXED, B),
            ["copper-plate=50", "iron-plate=200", "signal-A=7", "signal-A@uncommon=7", "water=9"]
        );
        assert_eq!(probe(qf(CmpOp::Ge), MIXED, B), ["iron-plate@epic=5", "iron-plate@rare=3", "signal-B@legendary=11"]);
    }

    #[test]
    fn item_modes_match_the_game() {
        items::set_space_age(false);
        let ins = &[("iron-plate", 1), ("iron-gear-wheel@rare", -5), ("nuclear-reactor", 1), ("water", 3), ("signal-A", 1), ("iron-plate@epic", 2)];
        assert_eq!(
            probe(Kind::Selector(Selector::StackSize), ins, &[]),
            ["iron-gear-wheel@rare=100", "iron-plate=100", "iron-plate@epic=100", "nuclear-reactor=10"]
        );
        let ins = &[("iron-plate", 1), ("iron-gear-wheel", 5), ("nuclear-reactor", 1), ("rocket-silo", 1)];
        assert_eq!(
            probe(Kind::Selector(Selector::RocketCapacity), ins, &[]),
            ["iron-gear-wheel=1000", "iron-plate=1000", "nuclear-reactor=1"]
        );
    }

    #[test]
    fn random_picks_an_input() {
        let eight: Vec<(String, i32)> = (1..=8).map(|k| (format!("signal-{k}"), k)).collect();
        let t = SignalTable::base();
        let mut n = Netlist::default();
        let c = n.add(Kind::Selector(Selector::Random { interval: 0 }), Role::Core);
        let k = n.add(Kind::Constant(ConstComb { values: eight.iter().map(|(s, v)| (t.lookup(s).unwrap(), *v)).collect(), on: true }), Role::Core);
        n.wire((k, Conn::Red), (c, Conn::InRed));
        let mut sim = Sim::new(&n);
        let mut seen = [0; 9];
        for _ in 0..400 {
            sim.step();
            let out = sim.outputs_of(c);
            if let [(s, v)] = out {
                assert_eq!(t.name(*s), format!("signal-{v}"));
                seen[*v as usize] += 1;
            }
        }
        assert!(seen[1..].iter().all(|n| *n > 20), "{seen:?}");
    }
}
