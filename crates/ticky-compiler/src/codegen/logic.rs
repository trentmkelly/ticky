//! The logic of step and period blocks ([`Cg::logic`]), read only once it has settled:
//! clusters with private red wires, gated selects, inlined conditions, sums on the wire
//! (`fold`/`transparent`/`absorbable`), direct bundle reads/writes, and the scalar
//! combinators themselves. (Every-tick blocks have their own emitter in `pipelined.rs`.)

use std::collections::{HashMap, VecDeque};

use ticky_factorio::*;
use ticky_syntax::{Diag, Span};

use super::*;
use super::selects::{self, Opd, Out};
use crate::ir::{BTerm, Graph, Op, V};

impl Cg {
    /// Emits combinators for every non-trivial node reachable from `roots`. `src` locates
    /// each source. Returns where each emitted node's value is.
    pub(super) fn logic(&mut self, g: &Graph, roots: &[V], src: &dyn Fn(u32) -> Ref, what: &str) -> Result<HashMap<V, Ref>, Diag> {
        let live: Vec<V> = g.reachable(roots);
        if std::env::var_os("TICKY_DUMP_IR").is_some() {
            eprintln!("== logic for {what}: {} nodes, roots {roots:?}", live.len());
            for &v in &live {
                eprintln!("  %{v} = {:?}", g.op(v));
            }
        }
        let is_scalar_op = |v: V| matches!(g.op(v), Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) | Op::Sel(_));
        let is_read = |v: V| matches!(g.op(v), Op::BGet(..) | Op::BTotal(_) | Op::BCount(_) | Op::AGet(..) | Op::BDot(..));
        let is_bun_op = |v: V| matches!(g.op(v), Op::BConst(_) | Op::Bun(_) | Op::BMux { .. } | Op::BDec(_) | Op::BSelect(..) | Op::BSelectAt(..) | Op::BSel(..));
        let producers: Vec<V> = live.iter().copied().filter(|v| is_scalar_op(*v) || is_read(*v) || is_bun_op(*v)).collect();
        let is_root: std::collections::HashSet<V> = roots.iter().copied().collect();

        // Selects become stages of deciders (see `selects.rs`): conditions inlined, arm
        // values passed through private wires, nested selects flattened.
        let mut pre: HashMap<V, Vec<V>> = HashMap::new();
        for &v in &producers {
            for o in g.operands(v) {
                pre.entry(o).or_default().push(v);
            }
        }
        let plan = selects::plan(g, &producers, &is_root, &pre);
        let inline_cond = &plan.inline_cond;
        // Each stage's passes, by value: (select, wire index — 0 for the cluster's own).
        let mut pass_of: HashMap<V, (V, usize)> = HashMap::new();
        for (&m, st) in &plan.stages {
            for (i, &x) in st.passes.iter().enumerate() {
                pass_of.insert(x, (m, i));
            }
        }
        // Operands as wired: a stage's reads; an inlined condition's own operands instead of it.
        let eff_operands = |v: V| -> Vec<V> {
            if let Some(st) = plan.stages.get(&v) {
                return st.all_reads();
            }
            g.operands(v).into_iter().flat_map(|o| if inline_cond.contains(&o) { g.operands(o) } else { vec![o] }).collect()
        };
        // Only what's still read: flattening and inlining leave some values unused.
        let producers: Vec<V> = {
            let set: std::collections::HashSet<V> = producers.iter().copied().filter(|v| !inline_cond.contains(v) && !plan.absorbed.contains(v)).collect();
            let mut needed: std::collections::HashSet<V> = Default::default();
            let mut stack: Vec<V> = roots.iter().copied().filter(|v| set.contains(v)).collect();
            while let Some(v) = stack.pop() {
                if needed.insert(v) {
                    stack.extend(eff_operands(v).into_iter().filter(|o| set.contains(o)));
                }
            }
            producers.into_iter().filter(|v| needed.contains(v)).collect()
        };
        if std::env::var_os("TICKY_DUMP_IR").is_some() {
            for &v in &producers {
                if let Some(st) = plan.stages.get(&v) {
                    eprintln!("  stage %{v}: passes {:?}", st.passes);
                    for (d, o) in &st.deciders {
                        eprintln!("    {o:?} if {d:?}");
                    }
                }
            }
        }

        // Split the logic into clusters of consecutive combinators. A value whose consumers
        // are all in its own cluster lives on that cluster's private red wire, where signal
        // names can be reused; everything else goes on the shared green bus. Values that
        // bundle combinators read must be on the bus (their red input carries the bundle).
        let mut cluster: HashMap<V, usize> = producers.iter().enumerate().map(|(i, v)| (*v, i / CLUSTER)).collect();
        // A passed value sits on its select's private wire.
        for (x, (m, _)) in &pass_of {
            let k = cluster[m];
            cluster.insert(*x, k);
        }
        let mut consumers: HashMap<V, Vec<V>> = HashMap::new();
        for &v in &producers {
            for o in eff_operands(v) {
                consumers.entry(o).or_default().push(v);
            }
        }
        let local = |v: V| -> bool {
            pass_of.contains_key(&v)
                || is_scalar_op(v)
                    && !is_root.contains(&v)
                    && !plan.has_pass(v)
                    && !plan.force_bus.contains(&v)
                    && consumers.get(&v).is_some_and(|cs| cs.iter().all(|c| is_scalar_op(*c) && cluster[c] == cluster[&v]))
        };
        // A value computed only to be one signal of a bundle (`{s: x, …}`) is written onto
        // the bundle's wire as that signal by the combinators computing it (no copy).
        let bundle_writes: HashMap<V, (V, Sig)> = producers
            .iter()
            .copied()
            .filter_map(|x| {
                if !is_scalar_op(x) || is_root.contains(&x) {
                    return None;
                }
                let [bun] = consumers.get(&x)?.as_slice() else { return None };
                let Op::Bun(terms) = g.op(*bun) else { return None };
                let mut sig = None;
                for t in terms {
                    match t {
                        BTerm::One(s, y) if *y == x && sig.is_none() => sig = Some(*s),
                        t if t.operands().contains(&x) => return None,
                        _ => {}
                    }
                }
                sig.map(|s| (x, (*bun, s)))
            })
            .collect();
        // Sums on the wire: combinators writing the same signal onto the same wire are
        // added for free, so `a + b` (and `a - b` when `b` can negate itself) needs no adder
        // when `a` and `b` are only used there: they write the sum's signal directly. This
        // logic is only read once it has settled (a step or block period), never pipelined,
        // so operands of different depths may meet on the wire.
        let single = |o: V| consumers.get(&o).is_some_and(|cs| cs.len() == 1) && !is_root.contains(&o);
        // `m` multiplies the node's value into the sum: -1 for a subtracted operand, `k` under
        // a `* k` (constants distribute over sums, wrapping included).
        fn absorbable(g: &Graph, o: V, m: i64, t: V, single: &dyn Fn(V) -> bool, same_place: &dyn Fn(V, V) -> bool, scalar: &dyn Fn(V) -> bool, local: &dyn Fn(V) -> bool) -> bool {
            let konst = |x: V| g.as_const(x);
            let fits = |k: i64| k > i32::MIN as i64 && k <= i32::MAX as i64;
            // A one-signal read (or total, or count) writes the sum's signal times the factor;
            // reads only write the bus, so the sum must be there.
            if matches!(g.op(o), Op::BGet(..) | Op::BTotal(_) | Op::BCount(_)) {
                return single(o) && same_place(o, t) && fits(m);
            }
            if !scalar(o) || !single(o) || !same_place(o, t) {
                return false;
            }
            match *g.op(o) {
                Op::Cmp(..) => fits(m),
                Op::Dec(ref arms) => arms.iter().all(|(_, k)| fits(*k as i64 * m)),
                Op::Mux { a, b, .. } if konst(a).is_some() && konst(b).is_some() => [a, b].iter().all(|x| fits(konst(*x).unwrap() as i64 * m)),
                Op::Sel(ref arms) if arms.iter().all(|(_, x)| konst(*x).is_some()) => arms.iter().all(|(_, x)| fits(konst(*x).unwrap() as i64 * m)),
                Op::Ar(ArOp::Sub, ..) if m == -1 => true,
                _ if m == 1 => true,
                Op::Ar(ArOp::Mul, x, y) => konst(x).or(konst(y)).is_some_and(|k| fits(k as i64 * m)),
                Op::Ar(ArOp::Div, _, y) if m == -1 => konst(y).is_some_and(|k| k != i32::MIN && k != 0),
                Op::Ar(op @ (ArOp::Add | ArOp::Sub), x, y) => {
                    let my = if op == ArOp::Sub { -m } else { m };
                    x != y && absorbable(g, x, m, t, single, same_place, scalar, local) && absorbable(g, y, my, t, single, same_place, scalar, local)
                }
                _ => false,
            }
        }
        // A node folded into a wire sum writes `(target, multiplier)`; a transparent sum (or a
        // `* k` pushed into its operand) emits nothing itself.
        let mut fold: HashMap<V, (V, i64)> = HashMap::new();
        // Gated selects pass a signal through under its own name, so can't write a sum's.
        let sum_op = |v: V| is_scalar_op(v) && !plan.has_pass(v);
        let mut transparent: std::collections::HashSet<V> = Default::default();
        {
            // Reads write the bus or a cluster wire, not a bundle's.
            let same_place = |o: V, t: V| if is_read(o) { !bundle_writes.contains_key(&t) } else { !local(t) || cluster.get(&o) == cluster.get(&t) };
            for &v in producers.iter().rev() {
                let (t, m) = fold.get(&v).copied().unwrap_or((v, 1));
                match *g.op(v) {
                    Op::Ar(op @ (ArOp::Add | ArOp::Sub), a, b) if a != b => {
                        let (ma, mb) = (m, if op == ArOp::Sub { -m } else { m });
                        if absorbable(g, a, ma, t, &single, &same_place, &sum_op, &local) && absorbable(g, b, mb, t, &single, &same_place, &sum_op, &local) {
                            transparent.insert(v);
                            fold.insert(a, (t, ma));
                            fold.insert(b, (t, mb));
                        }
                    }
                    // `x * k` with `x` a sum or condition that can take the factor itself.
                    Op::Ar(ArOp::Mul, a, b) => {
                        let (x, k) = match (g.as_const(a), g.as_const(b)) {
                            (None, Some(k)) => (a, k),
                            (Some(k), None) => (b, k),
                            _ => continue,
                        };
                        let mk = m * k as i64;
                        let pushable = matches!(g.op(x), Op::Cmp(..) | Op::Dec(_) | Op::Mux { .. } | Op::Sel(_) | Op::Ar(ArOp::Add | ArOp::Sub, ..) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_));
                        if pushable && mk.abs() <= i32::MAX as i64 && absorbable(g, x, mk, t, &single, &same_place, &sum_op, &local) {
                            transparent.insert(v);
                            fold.insert(x, (t, mk));
                        }
                    }
                    _ => {}
                }
            }
        }
        // One-signal reads used only by a bundle's copy or index term: that combinator reads
        // the signal from the bundle's wire itself.
        let direct_reads: HashMap<V, (V, Sig)> = producers
            .iter()
            .copied()
            .filter_map(|x| {
                let Op::BGet(b, s) = *g.op(x) else { return None };
                let cs = consumers.get(&x)?;
                let [bun] = cs.as_slice() else { return None };
                if is_root.contains(&x) || fold.contains_key(&x) {
                    return None;
                }
                let Op::Bun(terms) = g.op(*bun) else { return None };
                let only_copies = terms.iter().all(|t| match t {
                    BTerm::One(..) | BTerm::Shift(..) => true,
                    t => !t.operands().contains(&x),
                });
                only_copies.then_some((x, (b, s)))
            })
            .collect();
        let direct = |x: V| direct_reads.get(&x).copied();
        let mut node_ref: HashMap<V, Ref> = HashMap::new();
        let mut local_sig: HashMap<V, Sig> = HashMap::new();
        let mut local_pools: HashMap<usize, VecDeque<Sig>> = HashMap::new();
        // A select's bus signal is also its passed values' name on the private wires, so no
        // other value of that cluster may use it there. Further passes get wires of their own.
        let mut reserved: HashMap<usize, Vec<Sig>> = HashMap::new();
        let mut own_wire: HashMap<V, usize> = HashMap::new();
        for &m in &producers {
            if !plan.has_pass(m) {
                continue;
            }
            let s = match bundle_writes.get(&m) {
                Some((_, s)) => *s,
                None => self.alloc()?,
            };
            node_ref.insert(m, Ref::Op(Operand::Sig(s)));
            for (i, &x) in plan.stages[&m].passes.iter().enumerate() {
                local_sig.insert(x, s);
                if i > 0 {
                    self.nets.push(NetSpec { red: true, members: Vec::new() });
                    own_wire.insert(x, self.nets.len() - 1);
                }
            }
            reserved.entry(cluster[&m]).or_default().push(s);
        }
        for &v in &producers {
            if fold.contains_key(&v) || node_ref.contains_key(&v) || local_sig.contains_key(&v) || direct_reads.contains_key(&v) {
                continue;
            }
            if let Some((_, s)) = bundle_writes.get(&v) {
                node_ref.insert(v, Ref::Op(Operand::Sig(*s)));
                continue;
            }
            if is_bun_op(v) {
                node_ref.insert(v, Ref::Bun(self.bnew()));
            } else if local(v) {
                let res = reserved.get(&cluster[&v]).cloned().unwrap_or_default();
                let pool = local_pools.entry(cluster[&v]).or_insert_with(|| SignalTable::base().internal_pool().into_iter().filter(|s| !res.contains(s)).collect());
                let s = pool.pop_front().ok_or_else(|| Diag::error(Span::default(), "program too large: a logic cluster ran out of signals"))?;
                local_sig.insert(v, s);
            } else {
                node_ref.insert(v, Ref::Op(Operand::Sig(self.alloc()?)));
            }
        }
        // Where a value is, for combinators that read bundles (never cluster-local values).
        let locate = |u: V| -> Ref {
            let u = through_sig(g, u);
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
                self.emit_bundle(g, v, out, &locate, &direct, &|x| bundle_writes.contains_key(&x), what);
                continue;
            }
            if direct_reads.contains_key(&v) {
                continue;
            }
            if is_read(v) {
                let (t, m) = fold.get(&v).copied().unwrap_or((v, 1));
                let (out, net) = match local_sig.get(&t) {
                    Some(s) => {
                        let ni = match own_wire.get(&t) {
                            Some(&n) => n,
                            None => self.cluster_net(&mut cluster_net, cluster[&t]),
                        };
                        (*s, Some(ni))
                    }
                    None => (node_ref[&t].sig(), None),
                };
                self.emit_from_bundle(g, v, out, m as i32, net, &locate, what);
                continue;
            }
            if transparent.contains(&v) {
                continue;
            }
            let (target, m) = fold.get(&v).copied().unwrap_or((v, 1));
            let sign = m as i32;
            let out = match local_sig.get(&target) {
                Some(s) => *s,
                None => node_ref[&target].sig(),
            };
            let out_local = local(target);
            let out_bundle = bundle_writes.get(&target).map(|(bun, _)| node_ref[bun].bun());
            // Where a combinator's output goes: a bundle's wire, the bus, or (for a value that
            // lives on a private wire) that wire.
            let wire_out = |cg: &mut Cg, cluster_net: &mut HashMap<usize, usize>, id: EntId| {
                match out_bundle {
                    Some(b) => cg.bprod(b, id),
                    None if !out_local => cg.nets[0].members.push((id, Conn::OutGreen)),
                    None => {
                        let ni = match own_wire.get(&target) {
                            Some(&n) => n,
                            None => cg.cluster_net(cluster_net, cluster[&v]),
                        };
                        cg.nets[ni].members.push((id, Conn::OutRed));
                    }
                }
            };
            if let Some(st) = plan.stages.get(&v) {
                for (d, o) in &st.deciders {
                    let reads = selects::Stage::reads(d, o);
                    // The red wire it reads: a further pass's own, else the cluster's (a
                    // decider has one red input; the plan moved everything else to the bus).
                    let red = match reads.iter().find_map(|u| own_wire.get(u)) {
                        Some(&n) => Some(n),
                        None if reads.iter().any(|&u| local(u)) => Some(self.cluster_net(&mut cluster_net, cluster[&v])),
                        None => None,
                    };
                    let bus = if red.is_some() { Nets::GREEN } else { Nets::BOTH };
                    let pick = |u: V| -> (Operand, Nets) {
                        match *g.op(u) {
                            Op::Const(k) => (Operand::Const(k), Nets::BOTH),
                            Op::Src(s) => (src(s).op(), bus),
                            _ if local(u) => (Operand::Sig(local_sig[&u]), Nets::RED),
                            _ => (node_ref[&u].op(), bus),
                        }
                    };
                    let opnd = |o: Opd| match o {
                        Opd::K(k) => (Operand::Const(k), Nets::BOTH),
                        Opd::V(u) => pick(u),
                    };
                    let mut terms: CDnf = Vec::new();
                    'terms: for t in d {
                        let mut conds = Vec::new();
                        for l in t {
                            let (x, y) = (opnd(l.a), opnd(l.b));
                            let (cmp, (first, first_nets), (second, second_nets)) = match (x.0, y.0) {
                                (Operand::Sig(s), _) => (l.op, (s, x.1), y),
                                (Operand::Const(_), Operand::Sig(s)) => (l.op.flip(), (s, y.1), x),
                                (Operand::Const(p), Operand::Const(q)) if l.op.apply(p, q) => continue,
                                (Operand::Const(_), Operand::Const(_)) => continue 'terms,
                            };
                            conds.push(Cond { first, first_nets, second, second_nets, cmp, and: true });
                        }
                        assert!(!conds.is_empty(), "a select arm that always holds");
                        terms.push(conds);
                    }
                    let kind = match *o {
                        _ if terms.is_empty() && !matches!(o, Out::Mul(..)) => continue,
                        Out::K(k) => dec_const(distribute(&[], &terms), out, k * sign),
                        Out::Pass(_) => dec(distribute(&[], &terms), vec![DOut { sig: out, copy: true, constant: 0, nets: Nets::RED }]),
                        Out::Mul(x, c) => {
                            let ((first, first_nets), (second, second_nets)) = (pick(x), pick(c));
                            Kind::Arith(Arith { first, first_nets, second, second_nets, op: ArOp::Mul, out })
                        }
                    };
                    let id = self.net.add(kind, Role::Core);
                    self.net.entities[id].description = Some(format!("{what}: select"));
                    self.nets[0].members.push((id, Conn::InGreen));
                    if let Some(n) = red {
                        self.nets[n].members.push((id, Conn::InRed));
                    }
                    wire_out(self, &mut cluster_net, id);
                }
                continue;
            }
            let ops = eff_operands(v);
            let reads_local = ops.iter().any(|o| local(*o));
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
            // Negated (for a wire sum): a constant operand of `*` or `/` negates instead.
            let neg_const = |o: Operand| match o {
                Operand::Const(k) => Operand::Const(k.wrapping_neg()),
                o => o,
            };
            let mut kinds: Vec<(Kind, &str)> = Vec::new();
            match *g.op(v) {
                Op::Ar(ArOp::Sub, a, b) if sign == -1 => kinds.push((ar(b, ArOp::Sub, a), "arithmetic")),
                Op::Ar(ArOp::Div, a, b) if sign == -1 => {
                    let ((x, xn), (y, yn)) = (pick(a), pick(b));
                    kinds.push((Kind::Arith(Arith { first: x, first_nets: xn, second: neg_const(y), second_nets: yn, op: ArOp::Div, out }), "arithmetic"));
                }
                Op::Ar(ArOp::Mul, a, b) if sign != 1 => {
                    let ((x, xn), (y, yn)) = (pick(a), pick(b));
                    let scale = |o: Operand| match o {
                        Operand::Const(k) => Operand::Const(k.wrapping_mul(sign)),
                        o => o,
                    };
                    let (x, y) = if g.as_const(b).is_some() { (x, scale(y)) } else { (scale(x), y) };
                    kinds.push((Kind::Arith(Arith { first: x, first_nets: xn, second: y, second_nets: yn, op: ArOp::Mul, out }), "arithmetic"));
                }
                Op::Ar(op, a, b) => kinds.push((ar(a, op, b), "arithmetic")),
                Op::Cmp(op, a, b) => kinds.push((dec_const(vec![cond(a, op, b)], out, sign), "comparison")),
                Op::Dec(ref arms) => {
                    for (d, k) in arms {
                        let terms: CDnf = d.iter().map(|t| t.iter().map(|l| cond(l.a, l.op, l.b)).collect()).collect();
                        kinds.push((dec_const(distribute(&[], &terms), out, *k * sign), "condition"));
                    }
                }
                _ => unreachable!("not a scalar operation"),
            }
            for (kind, label) in kinds {
                let id = self.net.add(kind, Role::Core);
                self.net.entities[id].description = Some(format!("{what}: {label}"));
                self.nets[0].members.push((id, Conn::InGreen));
                if reads_local {
                    // Inputs from this node's cluster.
                    let ni = self.cluster_net(&mut cluster_net, cluster[&v]);
                    self.nets[ni].members.push((id, Conn::InRed));
                }
                // Output to its sum's wire (the same cluster whenever that is local).
                wire_out(self, &mut cluster_net, id);
            }
        }
        Ok(node_ref)
    }

    /// The red wire of logic cluster `k`, made when first needed.
    fn cluster_net(&mut self, nets: &mut HashMap<usize, usize>, k: usize) -> usize {
        *nets.entry(k).or_insert_with(|| {
            self.nets.push(NetSpec { red: true, members: Vec::new() });
            self.nets.len() - 1
        })
    }
}
