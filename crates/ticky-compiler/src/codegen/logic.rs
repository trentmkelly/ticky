//! The logic of step and period blocks ([`Cg::logic`]), read only once it has settled:
//! clusters with private red wires, gated selects, inlined conditions, sums on the wire
//! (`fold`/`transparent`/`absorbable`), direct bundle reads/writes, and the scalar
//! combinators themselves. (Every-tick blocks have their own emitter in `pipelined.rs`.)

use std::collections::{HashMap, VecDeque};

use ticky_factorio::*;
use ticky_syntax::{Diag, Span};

use super::*;
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

        // A comparison (or one-term condition) used only to choose constant arms of selects
        // isn't built: each arm's decider tests it itself (`K if x > 5 else …` is one decider
        // `x > 5 → K`, not a comparison plus a gate).
        let mut pre: HashMap<V, Vec<V>> = HashMap::new();
        for &v in &producers {
            for o in g.operands(v) {
                pre.entry(o).or_default().push(v);
            }
        }
        let boolean = |c: V| match g.op(c) {
            Op::Cmp(_, a, _) => g.as_const(*a).is_none(),
            Op::Dec(arms) => arms.len() == 1 && arms[0].1 == 1,
            _ => false,
        };
        // Gated selects: in `x if c else …` with `x` computed only for it, `x` is computed
        // straight onto the select's own signal on the cluster's private wire, and a decider
        // testing `c` passes it through to the bus (one decider, instead of a comparison and
        // a multiplier). One such arm per select; the select then lives on the bus.
        let mut gate: HashMap<V, (V, V)> = HashMap::new();
        for &m in &producers {
            let arms: Vec<(V, V)> = match g.op(m) {
                Op::Mux { t, f, a, b } => vec![(*t, *a), (*f, *b)],
                Op::Sel(arms) => arms.clone(),
                _ => continue,
            };
            let pick = arms.into_iter().find(|&(c, x)| {
                g.as_const(x).is_none()
                    && x != c
                    && is_scalar_op(x)
                    && !gate.contains_key(&x)
                    && !is_root.contains(&x)
                    && pre.get(&x).is_some_and(|cs| cs.as_slice() == [m])
                    && boolean(c)
            });
            if let Some(arm) = pick {
                gate.insert(m, arm);
            }
        }
        let inline_cond: std::collections::HashSet<V> = {
            producers
                .iter()
                .copied()
                .filter(|&c| {
                    boolean(c)
                        && !is_root.contains(&c)
                        && pre.get(&c).is_some_and(|cs| {
                            cs.iter().all(|&m| {
                                let arms: Vec<(V, V)> = match g.op(m) {
                                    Op::Mux { t, f, a, b } => vec![(*t, *a), (*f, *b)],
                                    Op::Sel(arms) => arms.clone(),
                                    _ => return false,
                                };
                                arms.iter().all(|&(cv, x)| match g.as_const(x) {
                                    Some(0) => true,
                                    _ if x == c => false,
                                    Some(_) => true,
                                    None => cv != c || gate.get(&m) == Some(&(cv, x)),
                                })
                            })
                        })
                })
                .collect()
        };
        // Operands as wired: an inlined condition's own operands instead of it.
        let eff_operands = |v: V| -> Vec<V> {
            g.operands(v).into_iter().flat_map(|o| if inline_cond.contains(&o) { g.operands(o) } else { vec![o] }).collect()
        };
        let producers: Vec<V> = producers.into_iter().filter(|v| !inline_cond.contains(v)).collect();

        // Split the logic into clusters of consecutive combinators. A value whose consumers
        // are all in its own cluster lives on that cluster's private red wire, where signal
        // names can be reused; everything else goes on the shared green bus. Values that
        // bundle combinators read must be on the bus (their red input carries the bundle).
        let mut cluster: HashMap<V, usize> = producers.iter().enumerate().map(|(i, v)| (*v, i / CLUSTER)).collect();
        // A gated value sits on its select's private wire.
        for (m, (_, x)) in &gate {
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
            is_scalar_op(v)
                && !is_root.contains(&v)
                && !gate.contains_key(&v)
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
        let sum_op = |v: V| is_scalar_op(v) && !gate.contains_key(&v);
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
        // A gated select's bus signal is also its value's name on the private wire, so no
        // other value of that cluster may use it there.
        let mut reserved: HashMap<usize, Vec<Sig>> = HashMap::new();
        for &m in &producers {
            if let Some((_, x)) = gate.get(&m) {
                let s = match bundle_writes.get(&m) {
                    Some((_, s)) => *s,
                    None => self.alloc()?,
                };
                node_ref.insert(m, Ref::Op(Operand::Sig(s)));
                local_sig.insert(*x, s);
                reserved.entry(cluster[&m]).or_default().push(s);
            }
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
                        let k = cluster[&t];
                        let ni = *cluster_net.entry(k).or_insert_with(|| {
                            self.nets.push(NetSpec { red: true, members: Vec::new() });
                            self.nets.len() - 1
                        });
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
            let ops = eff_operands(v);
            let reads_local = ops.iter().any(|o| local(*o));
            let out_local = local(target);
            let out_bundle = bundle_writes.get(&target).map(|(bun, _)| node_ref[bun].bun());
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
                Op::Mux { .. } | Op::Sel(_) => {
                    let arms: Vec<(V, V)> = match g.op(v) {
                        Op::Mux { t, f, a, b } => vec![(*t, *a), (*f, *b)],
                        Op::Sel(arms) => arms.clone(),
                        _ => unreachable!(),
                    };
                    for (cv, val) in arms {
                        if gate.get(&v) == Some(&(cv, val)) {
                            // The value is on the private wire under this select's signal.
                            let conds = match g.op(cv) {
                                Op::Cmp(op, a, b) if inline_cond.contains(&cv) => vec![cond(*a, *op, *b)],
                                Op::Dec(arms) if inline_cond.contains(&cv) => {
                                    let terms: CDnf = arms[0].0.iter().map(|t| t.iter().map(|l| cond(l.a, l.op, l.b)).collect()).collect();
                                    distribute(&[], &terms)
                                }
                                _ => {
                                    let (cs, cn) = sig(cv);
                                    vec![Cond { first: cs, first_nets: cn, ..c(cs, CmpOp::Ne, 0) }]
                                }
                            };
                            let pass = DOut { sig: out, copy: true, constant: 0, nets: Nets::RED };
                            kinds.push((dec(conds, vec![pass]), "select"));
                            continue;
                        }
                        match pick(val).0 {
                            Operand::Const(0) => {}
                            Operand::Const(k) if inline_cond.contains(&cv) => {
                                let conds = match g.op(cv) {
                                    Op::Cmp(op, a, b) => vec![cond(*a, *op, *b)],
                                    Op::Dec(arms) => {
                                        let terms: CDnf = arms[0].0.iter().map(|t| t.iter().map(|l| cond(l.a, l.op, l.b)).collect()).collect();
                                        distribute(&[], &terms)
                                    }
                                    _ => unreachable!("inlined condition"),
                                };
                                kinds.push((dec_const(conds, out, k * sign), "select"));
                            }
                            Operand::Const(k) => {
                                let (cs, cn) = sig(cv);
                                let cnd = Cond { first: cs, first_nets: cn, ..c(cs, CmpOp::Ne, 0) };
                                kinds.push((dec_const(vec![cnd], out, k * sign), "select"));
                            }
                            Operand::Sig(_) => kinds.push((ar(val, ArOp::Mul, cv), "select")),
                        }
                    }
                }
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
                match out_bundle {
                    Some(b) => self.bprod(b, id),
                    None if !out_local => self.nets[0].members.push((id, Conn::OutGreen)),
                    None => {}
                }
                if reads_local || out_local {
                    // Inputs from this node's cluster; output to its sum's (the same cluster
                    // whenever that is local).
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
}
