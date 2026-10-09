//! Tick-exact simulator for a [`Netlist`]: the same entities and wires that go into the
//! blueprint. Each tick, every wire network carries the sum of everything connected to it,
//! and every combinator computes its next output from the networks on its input side,
//! so an output becomes visible one tick after its inputs, as in Factorio.

use std::collections::HashMap;

use ticky_factorio::{Conn, EntId, Kind, Netlist, Nets, Operand, Sig, SignalTable};

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
        let slot = &mut self.dense[s.0 as usize];
        if *slot == 0 && v != 0 {
            self.touched.push(s.0);
        }
        *slot = slot.wrapping_add(v);
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
        let nsig = SignalTable::base().len();
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

    /// The value of `s` on the network attached to `e`'s connector `c` (as of the last tick).
    pub fn net_value(&self, e: EntId, c: Conn, s: Sig) -> i32 {
        self.nets[self.net(e, c)].dense[s.0 as usize]
    }

    fn read(&self, e: EntId, s: Sig, nets: Nets) -> i32 {
        let mut v = 0i32;
        if nets.red {
            v = v.wrapping_add(self.nets[self.net(e, Conn::InRed)].dense[s.0 as usize]);
        }
        if nets.green {
            v = v.wrapping_add(self.nets[self.net(e, Conn::InGreen)].dense[s.0 as usize]);
        }
        v
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
                Kind::Arith(_) | Kind::Decider(_) => {
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
                    let x = self.operand(e, a.first, a.first_nets);
                    let y = self.operand(e, a.second, a.second_nets);
                    let v = a.op.apply(x, y);
                    if v == 0 {
                        vec![]
                    } else {
                        vec![(a.out, v)]
                    }
                }
                Kind::Decider(d) => {
                    // OR of AND-groups.
                    let mut any = false;
                    let mut group = true;
                    for (i, c) in d.conds.iter().enumerate() {
                        if i > 0 && !c.and {
                            any |= group;
                            group = true;
                        }
                        let x = self.read(e, c.first, c.first_nets);
                        let y = self.operand(e, c.second, c.second_nets);
                        group &= c.cmp.apply(x, y);
                    }
                    any |= group && !d.conds.is_empty();
                    if !any {
                        vec![]
                    } else {
                        d.outputs
                            .iter()
                            .map(|o| (o.sig, if o.copy { self.read(e, o.sig, o.nets) } else { o.constant }))
                            .filter(|(_, v)| *v != 0)
                            .collect()
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
