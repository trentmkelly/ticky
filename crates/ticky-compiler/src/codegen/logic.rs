//! The logic of step and period blocks ([`Cg::logic`]), read only once it has settled:
//! clusters with private red wires, gated selects, inlined conditions, sums on the wire
//! (`fold`/`transparent`/`absorbable`), direct bundle reads/writes, staged values (written
//! under a register's signal onto its staging wire, see `registers::Cg::stage_loads`), and
//! the scalar combinators themselves. (Every-tick blocks have their own emitter in
//! `pipelined.rs`.)

use std::collections::{HashMap, VecDeque};

use ticky_factorio::*;
use ticky_syntax::{Diag, Span};

use super::*;
use super::selects::{self, Opd, Out};
use crate::fuse::slp;
use crate::ir::{BTerm, Graph, Op, V};

impl Cg {
    /// Emits combinators for every non-trivial node reachable from `roots`. `src` locates
    /// each source. Returns where each emitted node's value is.
    ///
    /// `staged`: roots to write under the given signal onto the given red wire instead (and
    /// not on the bus: they aren't in the result). Those this can't do are removed.
    pub(super) fn logic(&mut self, g: &Graph, roots: &[V], src: &dyn Fn(u32) -> Ref, staged: &mut HashMap<V, (Sig, usize)>, what: &str) -> Result<HashMap<V, Ref>, Diag> {
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
        // Each stage's passes, by value: (select, wire index — 0 for the cluster's own). Only
        // stages still read: a select flattened into another can keep a stage of its own that
        // passes the same values (or values nothing else reads).
        let mut pass_of: HashMap<V, (V, usize)> = HashMap::new();
        for &m in &producers {
            for (i, &x) in plan.stages.get(&m).map_or(&[][..], |st| &st.passes[..]).iter().enumerate() {
                pass_of.insert(x, (m, i));
            }
        }
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
        // Staged values: only roots nothing here reads (else they'd be needed on the bus).
        // A stage passing values names them on the cluster's wire by its own signal, here
        // the register's: at most one such stage per signal and cluster.
        {
            let mut named: std::collections::HashSet<(usize, Sig)> = Default::default();
            let mut ok: HashMap<V, (Sig, usize)> = HashMap::new();
            for &v in &producers {
                let Some(&(x, n)) = staged.get(&v) else { continue };
                let kind = is_scalar_op(v) || matches!(g.op(v), Op::BGet(..) | Op::BTotal(_) | Op::BCount(_));
                if kind && !consumers.contains_key(&v) && !pass_of.contains_key(&v) && (!plan.has_pass(v) || named.insert((cluster[&v], x))) {
                    ok.insert(v, (x, n));
                }
            }
            *staged = ok;
        }
        let staged = &*staged;
        // Floor division and modulo by a constant: the dividend is read from the bus.
        let mut floors = floor_groups(g, &producers, &|v| consumers.get(&v).cloned().unwrap_or_default());
        let floor_bus: std::collections::HashSet<V> = floors.iter().map(|f| f.a).collect();
        let local = |v: V| -> bool {
            pass_of.contains_key(&v)
                || staged.contains_key(&v)
                || is_scalar_op(v)
                    && !is_root.contains(&v)
                    && !plan.has_pass(v)
                    && !plan.force_bus.contains(&v)
                    && !floor_bus.contains(&v)
                    && consumers.get(&v).is_some_and(|cs| cs.iter().all(|c| is_scalar_op(*c) && cluster[c] == cluster[&v]))
        };
        // A value computed only to be one signal of a bundle (`{s: x, …}`) is written onto
        // the bundle's wire as that signal by the combinators computing it (no copy).
        let mut bundle_writes: HashMap<V, (V, Sig)> = producers
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
        // `x + s`, `s` a select with picks used only by the sum, `x` a value on the bus: `x`
        // joins `s`'s pick decider as an unconditional term (picks sum what passes) and the
        // decider writes the sum's signal. Python's `%` by a runtime divisor (`r + (d if r and
        // the signs differ else 0)`) is then one decider after the truncated `%`.
        let mut pick_addends: HashMap<V, V> = HashMap::new();
        let has_picks = |s: V| plan.stages.get(&s).is_some_and(|st| st.deciders.iter().any(|(_, o)| matches!(o, Out::Pick(_))));
        let picked_values = |s: V| -> Vec<V> { plan.stages[&s].deciders.iter().filter_map(|(_, o)| if let Out::Pick(x) = o { Some(*x) } else { None }).collect() };
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
                        } else if op == ArOp::Add && m == 1 && selects::pick_enabled() {
                            let addend = [(a, b), (b, a)].into_iter().find(|&(s, x)| {
                                has_picks(s)
                                    && !plan.has_pass(s)
                                    && single(s)
                                    && same_place(s, t)
                                    && !fold.contains_key(&s)
                                    && !pick_addends.contains_key(&s)
                                    && g.as_const(x).is_none()
                                    && !matches!(*g.op(x), Op::Src(i) if matches!(src(i), Ref::Op(Operand::Const(_))))
                                    && !local(x)
                                    && !pass_of.contains_key(&x)
                                    && !picked_values(s).contains(&x)
                            });
                            if let Some((s, x)) = addend {
                                transparent.insert(v);
                                fold.insert(s, (t, 1));
                                pick_addends.insert(s, x);
                            }
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
                    BTerm::One(..) | BTerm::Shift(..) | BTerm::HotEq(..) => true,
                    t => !t.operands().contains(&x),
                });
                only_copies.then_some((x, (b, s)))
            })
            .collect();
        let direct = |x: V| direct_reads.get(&x).copied();
        // A floor group's results, with their multipliers, must be on one private wire (where
        // its decider's corrections go).
        let wire_key = |t: V| match (staged.get(&t), pass_of.get(&t)) {
            (Some(&(_, n)), _) => (V::MAX - 1, n),
            (_, Some(&(_, i))) if i > 0 => (t, usize::MAX),
            _ => (V::MAX, cluster[&t]),
        };
        floors.retain_mut(|f| {
            if let Some((q, d, _)) = f.div {
                match fold.get(&d) {
                    Some(&(t, m)) if transparent.contains(&q) && (m == 1 || m == -1) && local(t) => f.div_to = Some((t, m as i32)),
                    _ => return false,
                }
            }
            if let Some((r, _)) = f.rem {
                match fold.get(&r).copied().unwrap_or((r, 1)) {
                    (t, 1) if !transparent.contains(&r) && local(t) => f.rem_to = Some(t),
                    _ => return false,
                }
            }
            let ts: Vec<V> = f.div_to.map(|(t, _)| t).into_iter().chain(f.rem_to).collect();
            ts.iter().all(|&t| wire_key(t) == wire_key(ts[0]))
        });
        // Members of a floor group: emitted with the group (and only the `%` result, a sum's
        // target, has a signal).
        let mut floor_at: HashMap<V, usize> = HashMap::new();
        for (i, f) in floors.iter().enumerate() {
            for v in [Some(f.m), f.div.map(|d| d.1), f.div.map(|d| d.2), f.rem.map(|r| r.0), f.rem.map(|r| r.1)].into_iter().flatten() {
                floor_at.insert(v, i);
            }
        }
        // A total of an arithmetic map/zip, or total/count of a filter, that nothing
        // else reads: its producer writes the scalar directly (bundles.rs `filter_total`).
        // Bundle producer → the read.
        let filter_totals: HashMap<V, V> = producers
            .iter()
            .copied()
            .filter(|&v| is_read(v))
            .filter_map(|v| {
                let m = fold.get(&v).map_or(1, |x| x.1);
                let b = Cg::filter_total(g, v, i32::try_from(m).ok()?)?;
                (consumers.get(&b).is_some_and(|cs| cs.as_slice() == [v]) && !is_root.contains(&b)).then_some((b, v))
            })
            .collect();
        let fused_total: std::collections::HashSet<V> = filter_totals.values().copied().collect();
        // A comparison or condition reading signals of one bundle that nothing else reads
        // (`ys[k] == zs[k] and …`) takes that bundle on its red input and the bus on green: no
        // read combinators. Not with cluster-local operands (they need the red input); not for
        // select stages or floor groups (their own emitters).
        let mut cond_reads: HashMap<V, V> = HashMap::new(); // decider → bundle
        let mut cond_read: HashMap<V, Sig> = HashMap::new(); // read → its signal
        for &v in &producers {
            if !matches!(g.op(v), Op::Cmp(..) | Op::Dec(_)) || transparent.contains(&v) || plan.stages.contains_key(&v) || floor_at.contains_key(&v) {
                continue;
            }
            let ops = eff_operands(v);
            if ops.iter().any(|o| local(*o)) {
                continue;
            }
            let reads: Vec<(V, V, Sig)> = ops
                .iter()
                .filter_map(|&o| match *g.op(o) {
                    Op::BGet(b, s)
                        if !is_root.contains(&o)
                            && !fold.contains_key(&o)
                            && !direct_reads.contains_key(&o)
                            && consumers.get(&o).is_some_and(|cs| cs.iter().all(|c| *c == v)) =>
                    {
                        Some((o, b, s))
                    }
                    _ => None,
                })
                .collect();
            // The bundle with the most such reads.
            let Some(b) = reads.iter().map(|r| r.1).max_by_key(|b| reads.iter().filter(|r| r.1 == *b).count()) else { continue };
            cond_reads.insert(v, b);
            for (o, rb, s) in reads {
                if rb == b {
                    cond_read.insert(o, s);
                }
            }
        }
        let mut node_ref: HashMap<V, Ref> = HashMap::new();
        let mut local_sig: HashMap<V, Sig> = HashMap::new();
        let mut local_pools: HashMap<usize, VecDeque<Sig>> = HashMap::new();
        // A select's bus signal is also its passed values' name on the private wires, so no
        // other value of that cluster may use it there. Further passes get wires of their own.
        let mut reserved: HashMap<usize, Vec<Sig>> = HashMap::new();
        let mut own_wire: HashMap<V, usize> = HashMap::new();
        for (&v, &(x, n)) in staged {
            local_sig.insert(v, x);
            own_wire.insert(v, n);
        }
        // Two selects of one cluster writing the same bundle signal (the same array element
        // in successive iterations of an unrolled loop) can't both name their passed values
        // after it on the cluster's wire, where they'd add up: later ones take a bus signal
        // and their bundle copies it. Nor can one share a staged stage's name (a register's
        // signal, which may be a bundle signal too).
        let mut named: std::collections::HashSet<(usize, Sig)> =
            producers.iter().filter(|m| plan.has_pass(**m)).filter_map(|m| staged.get(m).map(|&(x, _)| (cluster[m], x))).collect();
        for &m in &producers {
            if let Some(&(_, s)) = bundle_writes.get(&m).filter(|_| plan.has_pass(m)) {
                if !named.insert((cluster[&m], s)) {
                    bundle_writes.remove(&m);
                }
            }
        }
        let bundle_writes = bundle_writes;
        for &m in &producers {
            if !plan.has_pass(m) {
                continue;
            }
            let s = match (staged.get(&m), bundle_writes.get(&m)) {
                (Some(&(x, _)), _) => x,
                (_, Some((_, s))) => *s,
                _ => self.alloc()?,
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
        // A floor group's dividend signal carries its correction on the results' wire.
        let mut floor_sig: Vec<Option<Sig>> = Vec::new();
        // Signals on each staging wire: its staged values', then floor groups' dividends.
        let mut on_staging: HashMap<usize, Vec<Sig>> = HashMap::new();
        for &(x, n) in staged.values() {
            on_staging.entry(n).or_default().push(x);
        }
        for f in &floors {
            let a = match *g.op(f.a) {
                Op::Src(i) => src(i).sig(),
                _ => match node_ref.get(&f.a) {
                    Some(r) => r.sig(),
                    None => {
                        let s = self.alloc()?;
                        node_ref.insert(f.a, Ref::Op(Operand::Sig(s)));
                        s
                    }
                },
            };
            let t = f.div_to.map(|(t, _)| t).or(f.rem_to).unwrap();
            if let Some(&(_, n)) = staged.get(&t) {
                // With the loaded values (any of which may be a dividend's signal).
                let res = on_staging.entry(n).or_default();
                floor_sig.push((!res.contains(&a)).then_some(a));
                res.push(a);
            } else if own_wire.contains_key(&t) {
                // Alone on the wire with the select's signal.
                floor_sig.push((local_sig[&t] != a).then_some(a));
            } else {
                // (Two inputs on one signal, or an input on a select's signal: no.)
                let res = reserved.entry(cluster[&t]).or_default();
                floor_sig.push((!res.contains(&a)).then_some(a));
                res.push(a);
            }
        }
        // Straight-line vectorisation (fuse/slp.rs): same-shape operations done by one `each`
        // combinator, writing every lane's own signal where the lane's value would be (the bus
        // or its cluster's wire). A lane is an operation emitted on its own; its input must be a
        // combinator (or a sum of them, or a read) only it reads, which then writes the lane's
        // signal onto the pack's private wire instead.
        let mut lane_in: HashMap<V, usize> = HashMap::new();
        let mut packs: Vec<(slp::Pack, Option<usize>, usize, Vec<Sig>)> = Vec::new();
        if slp::enabled() {
            let writes_into = |t: V| floors.iter().any(|f| f.div_to.map(|d| d.0) == Some(t) || f.rem_to == Some(t));
            let placed = |v: V| {
                fold.contains_key(&v) || floor_at.contains_key(&v) || writes_into(v) || staged.contains_key(&v) || bundle_writes.contains_key(&v)
                    || plan.stages.contains_key(&v) || pass_of.contains_key(&v) || node_ref.contains_key(&v) || local_sig.contains_key(&v) || cond_reads.contains_key(&v)
                    || pick_addends.values().any(|&x| x == v)
            };
            let lane_ok = |v: V| !placed(v) && !transparent.contains(&v) && eff_operands(v) == g.operands(v);
            // Reads write a private wire too (`emit_from_bundle`'s `out_net`), unless they're
            // done by their consumer or fused into a sum.
            let input_free = |x: V| {
                let own = !is_root.contains(&x) && consumers.get(&x).is_some_and(|cs| cs.len() == 1);
                let scalar = is_scalar_op(x) && !placed(x);
                let read = is_read(x) && !fold.contains_key(&x) && !direct_reads.contains_key(&x) && !cond_read.contains_key(&x);
                own && (scalar || read)
            };
            let place = |v: V| if local(v) { Some(cluster[&v]) } else { None };
            for p in slp::plan(g, &producers, &lane_ok, &input_free, &place) {
                let at = place(p.lanes[0].out);
                self.nets.push(NetSpec { red: true, members: Vec::new() });
                let input = self.nets.len() - 1;
                let mut sigs = Vec::new();
                for l in &p.lanes {
                    let s = match at {
                        None => {
                            let s = self.alloc()?;
                            node_ref.insert(l.out, Ref::Op(Operand::Sig(s)));
                            s
                        }
                        Some(k) => {
                            let res = reserved.get(&k).cloned().unwrap_or_default();
                            let pool = local_pools.entry(k).or_insert_with(|| SignalTable::base().internal_pool().into_iter().filter(|s| !res.contains(s)).collect());
                            let s = pool.pop_front().ok_or_else(|| Diag::error(Span::default(), "program too large: a logic cluster ran out of signals"))?;
                            local_sig.insert(l.out, s);
                            s
                        }
                    };
                    node_ref.insert(l.input, Ref::Op(Operand::Sig(s)));
                    lane_in.insert(l.input, input);
                    sigs.push(s);
                }
                packs.push((p, at, input, sigs));
            }
        }
        let lanes: std::collections::HashSet<V> = packs.iter().flat_map(|p| p.0.lanes.iter().map(|l| l.out)).collect();
        // Each pack is placed where its last lane would have been, after all its inputs.
        let pack_at: HashMap<V, usize> = packs.iter().enumerate().map(|(i, p)| (producers.iter().rev().copied().find(|v| p.0.lanes.iter().any(|l| l.out == *v)).unwrap(), i)).collect();
        for &v in &producers {
            if fold.contains_key(&v) || node_ref.contains_key(&v) || local_sig.contains_key(&v) || direct_reads.contains_key(&v) || filter_totals.contains_key(&v) || cond_read.contains_key(&v) {
                continue;
            }
            if floor_at.get(&v).is_some_and(|&i| floor_sig[i].is_some() && floors[i].rem.map(|r| r.0) != Some(v)) {
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
        let mut shared_deciders: HashMap<Vec<(usize, Conn)>, Vec<EntId>> = HashMap::new();
        let mut floor_done: std::collections::HashSet<usize> = Default::default();
        // Combinators emitted per node, for `fuse::superopt::harvest` (superoptimiser targets).
        let mut marks: Vec<(V, EntId)> = Vec::new();

        for v in producers {
            marks.push((v, self.net.entities.len()));
            if filter_totals.contains_key(&v) {
                continue;
            }
            if let Some(&i) = floor_at.get(&v) {
                if let Some(a) = floor_sig[i] {
                    if floor_done.insert(i) {
                        self.emit_floor(&floors[i], a, &local_sig, &own_wire, &cluster, &mut cluster_net, what);
                    }
                    continue;
                }
            }
            if is_bun_op(v) {
                let out = node_ref[&v].bun();
                self.emit_bundle(g, v, out, &locate, &direct, &|x| bundle_writes.contains_key(&x), what);
                continue;
            }
            if direct_reads.contains_key(&v) || cond_read.contains_key(&v) {
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
                    None => (node_ref[&t].sig(), lane_in.get(&t).copied()),
                };
                if fused_total.contains(&v) {
                    self.emit_filter_total(g, v, out, m as i32, net, &locate, what);
                } else {
                    self.emit_from_bundle(g, v, out, m as i32, net, &locate, what);
                }
                continue;
            }
            if let Some(&i) = pack_at.get(&v) {
                let (p, at, input, sigs) = &packs[i];
                let out = at.map(|k| self.cluster_net(&mut cluster_net, k));
                self.emit_pack(p, sigs, *input, out, what);
            }
            if transparent.contains(&v) || lanes.contains(&v) {
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
            let out_lane = lane_in.get(&target).copied();
            let scalar_output = if out_bundle.is_some() || out_lane.is_some() {
                None
            } else if !out_local {
                Some((0, Conn::OutGreen))
            } else {
                let n = own_wire.get(&target).copied().unwrap_or_else(|| self.cluster_net(&mut cluster_net, cluster[&v]));
                Some((n, Conn::OutRed))
            };
            // Where a combinator's output goes: a bundle's wire, a pack's, the bus, or (for a
            // value that lives on a private wire) that wire.
            let wire_out = |cg: &mut Cg, cluster_net: &mut HashMap<usize, usize>, id: EntId| {
                match out_bundle {
                    Some(b) => cg.bprod(b, id),
                    None if out_lane.is_some() => cg.nets[out_lane.unwrap()].members.push((id, Conn::OutRed)),
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
                    if matches!(o, Out::Pick(_)) {
                        continue;
                    }
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
                        Out::Pick(_) => unreachable!("picks are emitted together"),
                    };
                    let id = self.net.add(kind, Role::Core);
                    self.net.entities[id].description = Some(format!("{what}: select"));
                    self.nets[0].members.push((id, Conn::InGreen));
                    if let Some(n) = red {
                        self.nets[n].members.push((id, Conn::InRed));
                    }
                    wire_out(self, &mut cluster_net, id);
                    if let Some(output) = scalar_output {
                        self.share_logic_decider(id, red, output, &mut shared_deciders);
                    }
                }
                // The stage's picks: one decider reading the bus and its code table.
                let picks: Vec<(&selects::SDnf, V)> = st.deciders.iter().filter_map(|(d, o)| if let Out::Pick(x) = *o { Some((d, x)) } else { None }).collect();
                let addend = pick_addends.get(&v).copied();
                if !picks.is_empty() {
                    assert_eq!(sign, 1, "a select with picks in a scaled wire sum");
                    let on_bus = |u: V| -> Operand {
                        match *g.op(u) {
                            Op::Const(k) => Operand::Const(k),
                            Op::Src(s) => src(s).op(),
                            _ => {
                                assert!(!local(u), "a value picks read is on a private wire");
                                node_ref[&u].op()
                            }
                        }
                    };
                    for id in self.emit_picks(&picks, addend, &on_bus, out, what) {
                        wire_out(self, &mut cluster_net, id);
                    }
                }
                continue;
            }
            let ops = eff_operands(v);
            let reads_local = ops.iter().any(|o| local(*o));
            // With a red input (cluster wire or a bundle's), every operand must say which wire
            // it comes from.
            let red_in = reads_local || cond_reads.contains_key(&v);
            let pick = |u: V| -> (Operand, Nets) {
                match *g.op(u) {
                    Op::Const(k) => (Operand::Const(k), Nets::BOTH),
                    Op::Src(s) => (src(s).op(), if red_in { Nets::GREEN } else { Nets::BOTH }),
                    _ if local(u) => (Operand::Sig(local_sig[&u]), Nets::RED),
                    _ if cond_read.contains_key(&u) => (Operand::Sig(cond_read[&u]), Nets::RED),
                    _ => (node_ref[&u].op(), if red_in { Nets::GREEN } else { Nets::BOTH }),
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
                if let Some(&b) = cond_reads.get(&v) {
                    let rb = locate(b).bun();
                    self.bread(rb, id, false);
                }
                if reads_local {
                    // Inputs from this node's cluster.
                    let ni = self.cluster_net(&mut cluster_net, cluster[&v]);
                    self.nets[ni].members.push((id, Conn::InRed));
                }
                // Output to its sum's wire (the same cluster whenever that is local).
                wire_out(self, &mut cluster_net, id);
                // Bundle readers have wiring outside the scalar cluster model.
                if let Some(output) = scalar_output.filter(|_| !cond_reads.contains_key(&v)) {
                    let red = reads_local.then(|| cluster_net[&cluster[&v]]);
                    self.share_logic_decider(id, red, output, &mut shared_deciders);
                }
            }
        }
        for v in staged.keys().chain(lane_in.keys()) {
            node_ref.remove(v);
        }
        if crate::fuse::superopt::harvesting() {
            crate::fuse::superopt::harvest(g, &live, roots, &marks, &self.net, what);
        }
        Ok(node_ref)
    }

    /// A straight-line pack (fuse/slp.rs): each lane's input writes the lane's signal onto the
    /// pack's private (red) wire `input`; the combinator computes every lane at once onto the
    /// bus, or the cluster wire `out`, with per-lane constants on its green input for a table.
    fn emit_pack(&mut self, p: &slp::Pack, sigs: &[Sig], input: usize, out: Option<usize>, what: &str) {
        let each = self.each;
        let lanes = Operand::Sig(each);
        let k = Operand::Const(p.lanes[0].k);
        let kind = match p.op {
            slp::PackOp::Ar { op, left: false } if !p.table => Kind::Arith(Arith { first: lanes, first_nets: Nets::RED, second: k, second_nets: Nets::BOTH, op, out: each }),
            slp::PackOp::Ar { op, left: true } if !p.table => Kind::Arith(Arith { first: k, first_nets: Nets::BOTH, second: lanes, second_nets: Nets::RED, op, out: each }),
            slp::PackOp::Ar { op, left } => {
                let (red, green) = ((lanes, Nets::RED), (lanes, Nets::GREEN));
                let ((first, first_nets), (second, second_nets)) = if left { (green, red) } else { (red, green) };
                Kind::Arith(Arith { first, first_nets, second, second_nets, op, out: each })
            }
            slp::PackOp::Cmp(cmp) => dec(vec![Cond { first: each, first_nets: Nets::RED, second: k, second_nets: Nets::BOTH, cmp, and: true }], vec![out_const(each, 1)]),
        };
        let id = self.loose(kind, format!("{what}: {} lanes at once", p.lanes.len()));
        self.nets[input].members.push((id, Conn::InRed));
        match out {
            None => self.nets[0].members.push((id, Conn::OutGreen)),
            Some(n) => self.nets[n].members.push((id, Conn::OutRed)),
        }
        if p.table {
            let consts = self.bnew();
            let values = crate::ir::normalize(sigs.iter().zip(&p.lanes).map(|(s, l)| (*s, l.k)));
            let kc = self.loose(Kind::Constant(ConstComb { values, on: true }), format!("{what}: lane constants"));
            self.bprod(consts, kc);
            self.bread(consts, id, true);
        }
    }

    /// A stage's picks (`selects::Out::Pick`): one decider copying the arm whose condition holds
    /// off the bus (green) onto `out`, its red input a constant giving each arm's signal a code;
    /// terms `each(red) = code ∧ the arm's literals (green)`. With `each` in the conditions, the
    /// single output sums the passing signals' green values: the arm value, renamed. Arms whose
    /// value turns out constant (a source with no signal) get a constant decider of their own.
    /// `addend`: a value always added (a term with its code alone). Returns the deciders made
    /// (all reading the bus; outputs not wired yet).
    fn emit_picks(&mut self, picks: &[(&selects::SDnf, V)], addend: Option<V>, on_bus: &dyn Fn(V) -> Operand, out: Sig, what: &str) -> Vec<EntId> {
        let each = self.each;
        // `None`: a literal that always holds; `Err(())`: one that never does.
        let lit = |l: &selects::SLit| -> Result<Option<Cond>, ()> {
            let opnd = |o: Opd| match o {
                Opd::K(k) => Operand::Const(k),
                Opd::V(u) => on_bus(u),
            };
            match (opnd(l.a), opnd(l.b)) {
                (Operand::Sig(s), y) => Ok(Some(Cond { first: s, first_nets: Nets::GREEN, second: y, second_nets: Nets::GREEN, cmp: l.op, and: true })),
                (Operand::Const(p), Operand::Sig(s)) => Ok(Some(Cond { first: s, first_nets: Nets::GREEN, second: Operand::Const(p), second_nets: Nets::GREEN, cmp: l.op.flip(), and: true })),
                (Operand::Const(p), Operand::Const(q)) => if l.op.apply(p, q) { Ok(None) } else { Err(()) },
            }
        };
        let terms_of = |d: &selects::SDnf, prefix: Option<Cond>| -> CDnf {
            let mut terms = Vec::new();
            'terms: for t in d {
                let mut conds: Vec<Cond> = prefix.iter().cloned().collect();
                for l in t {
                    match lit(l) {
                        Ok(Some(c)) => conds.push(c),
                        Ok(None) => {}
                        Err(()) => continue 'terms,
                    }
                }
                if conds.is_empty() {
                    // Always true (no literal reads a signal): tests a signal that's never there.
                    conds.push(Cond { first: out, first_nets: Nets::RED, second: Operand::Const(0), second_nets: Nets::BOTH, cmp: CmpOp::Eq, and: true });
                }
                terms.push(conds);
            }
            terms
        };
        let mut codes: Vec<(Sig, i32)> = Vec::new();
        let mut terms: CDnf = Vec::new();
        let mut made = Vec::new();
        for &(d, x) in picks {
            match on_bus(x) {
                Operand::Const(0) => {}
                Operand::Const(k) => {
                    let t = terms_of(d, None);
                    if !t.is_empty() {
                        let id = self.loose(dec_const(distribute(&[], &t), out, k), format!("{what}: select"));
                        self.nets[0].members.push((id, Conn::InGreen));
                        made.push(id);
                    }
                }
                Operand::Sig(s) => {
                    let code = match codes.iter().find(|c| c.0 == s) {
                        Some(c) => c.1,
                        None => {
                            codes.push((s, codes.len() as i32 + 1));
                            codes.len() as i32
                        }
                    };
                    let prefix = Cond { first: each, first_nets: Nets::RED, second: Operand::Const(code), second_nets: Nets::BOTH, cmp: CmpOp::Eq, and: true };
                    terms.extend(terms_of(d, Some(prefix)));
                }
            }
        }
        match addend.map(on_bus) {
            None | Some(Operand::Const(0)) => {}
            Some(Operand::Const(_)) => unreachable!("pick addends are signals (logic: `pick_addends`)"),
            Some(Operand::Sig(s)) => {
                // Its own code: a signal already picked would pass once, not twice.
                assert!(codes.iter().all(|c| c.0 != s), "a pick's addend is one of its arms");
                codes.push((s, codes.len() as i32 + 1));
                let code = codes.len() as i32;
                terms.push(vec![Cond { first: each, first_nets: Nets::RED, second: Operand::Const(code), second_nets: Nets::BOTH, cmp: CmpOp::Eq, and: true }]);
            }
        }
        if !terms.is_empty() {
            let kind = dec(distribute(&[], &terms), vec![DOut { sig: out, copy: true, constant: 0, nets: Nets::GREEN }]);
            let id = self.loose(kind, format!("{what}: select (picks {} off the bus)", if codes.len() == 1 { "1 value".to_string() } else { format!("{} values", codes.len()) }));
            let table = self.loose(Kind::Constant(ConstComb { values: crate::ir::normalize(codes), on: true }), format!("{what}: select codes"));
            self.nets[0].members.push((id, Conn::InGreen));
            self.nets.push(NetSpec { red: true, members: vec![(table, Conn::Red), (id, Conn::InRed)] });
            made.push(id);
        }
        made
    }

    /// Share only constant-output scalar deciders on exactly the same physical networks.
    /// The newest entity has no published entity-id references beyond these connectors;
    /// removing it leaves all earlier ids intact. Bundle producers/readers stay separate.
    fn share_logic_decider(&mut self, id: EntId, red: Option<usize>, output: (usize, Conn), seen: &mut HashMap<Vec<(usize, Conn)>, Vec<EntId>>) {
        let Kind::Decider(d) = &self.net.entities[id].kind else {
            return;
        };
        if d.outputs.iter().any(|o| o.copy) {
            return;
        }
        let mut wires = vec![(0, Conn::InGreen), output];
        if let Some(n) = red {
            wires.push((n, Conn::InRed));
        }
        let candidates = seen.entry(wires.clone()).or_default();
        let same = candidates.iter().copied().find(|&other| {
            let Kind::Decider(old) = &self.net.entities[other].kind else { unreachable!() };
            old.conds == d.conds && d.outputs.iter().all(|o| old.outputs.iter().all(|p| p.sig != o.sig))
        });
        let Some(other) = same else {
            candidates.push(id);
            return;
        };
        assert_eq!(id + 1, self.net.entities.len());
        let removed = self.net.entities.pop().unwrap();
        let Kind::Decider(d) = removed.kind else { unreachable!() };
        let Kind::Decider(old) = &mut self.net.entities[other].kind else { unreachable!() };
        old.outputs.extend(d.outputs);
        if let Some(desc) = removed.description {
            self.net.entities[other].description.get_or_insert_default().push_str(&format!("; {desc}"));
        }
        for (n, _) in wires {
            self.nets[n].members.retain(|(e, _)| *e != id);
        }
    }

    /// A floor group (see [`Floor`]): the decider and the divider(s).
    fn emit_floor(&mut self, f: &Floor, a: Sig, local_sig: &HashMap<V, Sig>, own_wire: &HashMap<V, usize>, cluster: &HashMap<V, usize>, cluster_net: &mut HashMap<usize, usize>, what: &str) {
        let t = f.div_to.map(|(t, _)| t).or(f.rem_to).unwrap();
        let wire = match own_wire.get(&t) {
            Some(&n) => n,
            None => self.cluster_net(cluster_net, cluster[&t]),
        };
        let (cmp, s) = if f.k > 0 { (CmpOp::Lt, 1) } else { (CmpOp::Gt, -1) };
        let mut outs = vec![out_const(a, s)];
        let mut ops = Vec::new();
        if let Some((t, m)) = f.div_to {
            outs.push(out_const(local_sig[&t], -m));
            ops.push((ArOp::Div, f.k * m, local_sig[&t], "floor division"));
        }
        if let Some(t) = f.rem_to {
            outs.push(out_const(local_sig[&t], if f.k > 0 { f.k - 1 } else { f.k + 1 }));
            ops.push((ArOp::Mod, f.k, local_sig[&t], "floor modulo"));
        }
        let id = self.net.add(dec(vec![cnd(a, cmp)], outs), Role::Core);
        self.net.entities[id].description = Some(format!("{what}: floor correction"));
        self.nets[0].members.push((id, Conn::InGreen));
        self.nets[wire].members.push((id, Conn::OutRed));
        for (op, k, out, label) in ops {
            // The dividend from the bus plus its correction from the wire (both colours).
            let id = self.net.add(arith(Operand::Sig(a), op, Operand::Const(k), out), Role::Core);
            self.net.entities[id].description = Some(format!("{what}: {label}"));
            self.nets[0].members.push((id, Conn::InGreen));
            self.nets[wire].members.push((id, Conn::InRed));
            self.nets[wire].members.push((id, Conn::OutRed));
        }
    }

    /// The red wire of logic cluster `k`, made when first needed.
    fn cluster_net(&mut self, nets: &mut HashMap<usize, usize>, k: usize) -> usize {
        *nets.entry(k).or_insert_with(|| {
            self.nets.push(NetSpec { red: true, members: Vec::new() });
            self.nets.len() - 1
        })
    }
}

/// Python `//` and `%` by a constant `k` (lowered as `q - [r < 0]` and `r + k·[r < 0]`, with
/// `q`, `r` the truncated quotient and remainder; `>` when k < 0) as one decider and the
/// divider(s): with c = [a < 0],
///
///   a // k = tdiv(a + c, k) − c        a % k = tmod(a + c, k) + (k − 1)·c
///
/// (k < 0: c = [a > 0], a − c, and k + 1). Exact over the whole range, INT_MIN included. The
/// decider reads `a` from the bus and writes ±c onto `a`'s own signal on the results' private
/// wire, where the dividers read it summed with `a` from the bus, plus the corrections onto
/// the results.
pub(super) struct Floor {
    a: V,
    k: i32,
    /// The truncated remainder (`Mod`).
    m: V,
    /// `//`: the result `q - [r < 0]`, the quotient, the comparison.
    div: Option<(V, V, V)>,
    /// `%`: the result `r + k·[r < 0]`, the condition.
    rem: Option<(V, V)>,
    /// Where the results go (wire sums): the quotient's target and multiplier (±1), the
    /// remainder's target (multiplier 1).
    div_to: Option<(V, i32)>,
    rem_to: Option<V>,
}

/// Floor groups by dividend (one per dividend: two would add their corrections together).
fn floor_groups(g: &Graph, producers: &[V], users: &dyn Fn(V) -> Vec<V>) -> Vec<Floor> {
    let mut out: Vec<Floor> = Vec::new();
    let zero = |v: V| g.as_const(v) == Some(0);
    let only = |v: V| -> Option<V> {
        let mut u = users(v);
        u.dedup();
        match u.as_slice() {
            [x] => Some(*x),
            _ => None,
        }
    };
    for &m in producers {
        let Op::Ar(ArOp::Mod, a, kv) = *g.op(m) else { continue };
        let Some(k) = g.as_const(kv) else { continue };
        if g.as_const(a).is_some() || matches!(k, -1..=1 | i32::MIN) || out.iter().any(|f| f.a == a) {
            continue;
        }
        let op = if k > 0 { CmpOp::Lt } else { CmpOp::Gt };
        let (mut div, mut rem) = (None, None);
        let mut mu = users(m);
        mu.sort_unstable();
        mu.dedup();
        for &u in &mu {
            match g.op(u) {
                Op::Cmp(o, x, z) if *o == op && *x == m && zero(*z) => {
                    let Some(q) = only(u) else { continue };
                    if let Op::Ar(ArOp::Sub, d, c) = *g.op(q) {
                        if c == u && matches!(*g.op(d), Op::Ar(ArOp::Div, a2, k2) if a2 == a && k2 == kv) && only(d) == Some(q) {
                            div = Some((q, d, u));
                        }
                    }
                }
                Op::Dec(arms) if matches!(arms.as_slice(), [(d, kk)] if *kk == k && matches!(d.as_slice(), [t] if matches!(t.as_slice(), [l] if l.op == op && l.a == m && zero(l.b)))) => {
                    let Some(r) = only(u) else { continue };
                    if matches!(*g.op(r), Op::Ar(ArOp::Add, x, y) if (x, y) == (m, u) || (x, y) == (u, m)) {
                        rem = Some((r, u));
                    }
                }
                _ => {}
            }
        }
        let inside = [div.map(|d: (V, V, V)| d.2), rem.map(|r: (V, V)| r.0), rem.map(|r: (V, V)| r.1)];
        if (div.is_some() || rem.is_some()) && mu.iter().all(|u| inside.contains(&Some(*u))) {
            out.push(Floor { a, k, m, div, rem, div_to: None, rem_to: None });
        }
    }
    out
}
