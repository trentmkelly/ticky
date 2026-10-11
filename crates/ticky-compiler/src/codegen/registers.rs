//! State-holding machinery: registers (hold decider + guarded loads, scalar and bundle),
//! sample registers, the step-timer style counter and the every-tick accumulator.
//!
//! Deciders that differ only in their outputs are built once with all the outputs
//! ([`Cg::shared`]): the holds of registers held under the same conditions (`[conds] → x
//! copy, y copy, …`), every initial value (`[ST≠0] → x = 1, y = 5, …`), and loads that
//! commit together (`[en≠0 ∧ guard] → x = 3, y copy, …`).
//!
//! **Staged loads** ([`Cg::stage_loads`]): a value used only by one load is computed by
//! `logic()` under the register's own signal onto a private red staging wire, and the load
//! is a decider copying it from there (`[en≠0 ∧ guard] → x copy`, conditions read from the
//! bus). A guarded one checks its guard on the commit tick (like direct constant loads),
//! so it needs no enable decider; loads with the same commit and guard share the decider.
//! Guards of the same register's loads may test the staged value itself, read from the
//! wire under the register's signal: `x = max(a - b, 0)` is `a - b → x` onto the wire,
//! `[en ∧ x(red) > 0] → x copy` and `[en ∧ x(red) ≤ 0] → x = 0`.

use std::collections::{HashMap, HashSet};

use ticky_factorio::*;
use ticky_syntax::Diag;

use super::*;
use crate::fuse::{is_true, keep_of, LoadVal, WriterPlan};
use crate::ir::{Graph, Lit, Op, V};
use crate::program::SrcKind;

/// A decider waiting for others with the same conditions. `red`: the staging wire its copy
/// outputs read (its conditions then read the bus only).
#[derive(Clone)]
pub(super) struct Pending {
    conds: Vec<Cond>,
    outs: Vec<DOut>,
    descs: Vec<String>,
    red: Option<usize>,
}

impl Cg {
    /// A decider `[conds] → out`, merged with every other one of the same conditions in this
    /// block or process (program-wide when the conditions only test RUN, RP and ST). The
    /// outputs must be on distinct signals. Built by [`Cg::flush_shared`].
    pub(super) fn shared(&mut self, conds: Vec<Cond>, out: DOut, desc: impl Into<String>) {
        self.shared_on(conds, out, None, desc);
    }

    /// [`Cg::shared`] for a decider whose red input is wire `red` (if any): constant outputs
    /// join any decider of the same conditions, copies only one on the same wire.
    fn shared_on(&mut self, conds: Vec<Cond>, out: DOut, red: Option<usize>, desc: impl Into<String>) {
        let desc = desc.into();
        let fits = |p: &Pending| p.red == red || red.is_none() && !out.copy || p.red.is_none() && p.outs.iter().all(|o| !o.copy);
        match self.pending.iter_mut().find(|p| p.conds == conds && fits(p)) {
            Some(p) => {
                p.outs.push(out);
                p.descs.push(desc);
                p.red = p.red.or(red);
            }
            None => self.pending.push(Pending { conds, outs: vec![out], descs: vec![desc], red }),
        }
    }

    /// A load's decider `[en≠0 ∧ guard] → out` (shared with every other one of the same
    /// conditions), its red input `red`. `guard` as from [`guard_conds`].
    fn load_decider(&mut self, en: Sig, guard: &CDnf, out: DOut, red: Option<usize>, desc: String) {
        self.shared_on(distribute(&[green(c(en, CmpOp::Ne, 0))], guard), out, red, desc);
    }

    /// An enable pulse timed like writer `w`'s commit pulse, but only when `guard` holds (read
    /// one tick earlier). Loads under the same conditions share one.
    fn load_condition(&mut self, w: &Writer, guard: &crate::ir::Dnf, desc: String) -> Result<Sig, Diag> {
        let conds = distribute(&w.prefix, &lits(guard, w.lit_eg));
        if let Some((_, eg)) = self.egs.iter().find(|(k, _)| *k == conds) {
            return Ok(*eg);
        }
        let eg = self.alloc()?;
        self.core(dec_const(conds.clone(), eg, 1), desc);
        self.egs.push((conds, eg));
        Ok(eg)
    }

    /// Register `x` holds (copies itself) while `conds` hold.
    pub(super) fn hold(&mut self, conds: Vec<Cond>, x: Sig, name: &str) {
        self.shared(conds, DOut { sig: x, copy: true, constant: 1, nets: Nets::BOTH }, format!("{name} (hold)"));
    }

    /// Builds the pending shared deciders: those local to the block or process just built,
    /// or (`all`) every one.
    pub(super) fn flush_shared(&mut self, all: bool) {
        let global = [self.run, self.rp, self.st];
        let (now, keep): (Vec<Pending>, Vec<Pending>) =
            std::mem::take(&mut self.pending).into_iter().partition(|p| all || !p.conds.iter().all(|c| global.contains(&c.first)));
        self.pending = keep;
        self.egs.clear();
        for p in now {
            let id = self.core(dec(p.conds, p.outs), p.descs.join("; "));
            if let Some(n) = p.red {
                self.nets[n].members.push((id, Conn::InRed));
            }
        }
    }

    /// `sig` counts up by one every tick while `conds` hold, and is 0 otherwise. A decider
    /// copies the signal from a private red loop that also carries a constant +1.
    pub(super) fn counter(&mut self, sig: Sig, conds: Vec<Cond>, desc: &str) {
        let d = self.core(dec(conds, vec![DOut { sig, copy: true, constant: 1, nets: Nets::RED }]), desc);
        let k = self.net.add(Kind::Constant(ConstComb { values: vec![(sig, 1)], on: true }), Role::Core);
        self.net.entities[k].description = Some(format!("{desc} (+1)"));
        self.nets.push(NetSpec { red: true, members: vec![(d, Conn::InRed), (d, Conn::OutRed), (k, Conn::Red)] });
    }

    /// A register on signal `x`, updated by `writers`. Each writer has a commit pulse `en`
    /// (visible on the commit tick), the conditions that produce that pulse one tick earlier
    /// (`prefix`, used to time enable pulses for guarded loads) and a plan. When no load
    /// fires, the register holds. ST loads `init`.
    pub(super) fn register(&mut self, x: Sig, init: i32, writers: &[Writer], name: &str) -> Result<(), Diag> {
        self.register_incs(x, init, writers, &[], name)
    }

    /// [`Cg::register`], where `incs[w][l]` marks writer `w`'s load `l` as an increment (see
    /// [`increments`]): it adds its value while the register keeps holding. Constant
    /// increments check their guard on the commit tick (one decider each), as do staged
    /// loads (`Writer::stage`).
    pub(super) fn register_incs(&mut self, x: Sig, init: i32, writers: &[Writer], incs: &[Vec<bool>], name: &str) -> Result<(), Diag> {
        let mut hold: CDnf = vec![vec![c(self.st, CmpOp::Eq, 0), c(self.run, CmpOp::Ne, 0)]];
        for (wi, w) in writers.iter().enumerate() {
            let inc = |l: usize| incs.get(wi).is_some_and(|i| i[l]);
            let unconditional = w.plan.loads.len() == 1 && is_true(&w.plan.loads[0].guard);
            let mut factor: CDnf = vec![vec![]];
            if unconditional && !inc(0) {
                factor = vec![vec![c(w.en, CmpOp::Eq, 0)]];
            }
            for (li, l) in w.plan.loads.iter().enumerate() {
                let stage = w.stage.get(li).copied().flatten();
                let red = stage.map(|s| s.wire);
                // (Only for loads read on the commit tick: pipelined blocks have no commit-tick
                // value of other loads' guards.)
                let guard = || guard_conds(w, &l.guard, x, stage);
                if stage.is_some_and(|s| s.copy) {
                    // Staged: copied from the wire on the commit tick when the guard holds. The
                    // hold is as for any load (increments keep it; a guarded load is direct).
                    let what = if inc(li) { "increment" } else { "load" };
                    let copy = DOut { sig: x, copy: true, constant: 1, nets: Nets::RED };
                    self.load_decider(w.en, &guard(), copy, red, format!("{name} (staged {what})"));
                    continue;
                }
                if inc(li) {
                    match l.val {
                        LoadVal::Const(0) => {}
                        LoadVal::Const(k) => {
                            self.load_decider(w.en, &guard(), out_const(x, k), red, format!("{name} (increment)"));
                        }
                        LoadVal::Node(v) => {
                            let en = if is_true(&l.guard) { w.en } else { self.load_condition(w, &l.guard, format!("{name} (increment condition)"))? };
                            let s = (w.val)(v).sig();
                            self.core(arith(Operand::Sig(s), ArOp::Mul, Operand::Sig(en), x), format!("{name} (increment)"));
                        }
                    }
                    continue;
                }
                if unconditional {
                    match l.val {
                        LoadVal::Const(0) => {}
                        LoadVal::Const(k) => {
                            self.load_decider(w.en, &vec![vec![]], out_const(x, k), None, format!("{name} (load)"));
                        }
                        LoadVal::Node(v) => {
                            let s = (w.val)(v).sig();
                            self.core(arith(Operand::Sig(s), ArOp::Mul, Operand::Sig(w.en), x), format!("{name} (load)"));
                        }
                    }
                    continue;
                }
                if let (true, LoadVal::Const(k)) = (l.direct, &l.val) {
                    // Checked on the commit tick by the load decider itself.
                    if *k != 0 {
                        self.load_decider(w.en, &guard(), out_const(x, *k), red, format!("{name} (conditional load)"));
                    }
                    continue;
                }
                // An enable pulse timed like the commit pulse, but only when the guard holds.
                // (A direct value load that `logic()` couldn't stage comes here too: the hold's
                // `keep` then also tests its guard, which is harmless as it stops the hold.)
                let eg = self.load_condition(w, &l.guard, format!("{name} (load condition)"))?;
                match l.val {
                    LoadVal::Const(0) => {}
                    LoadVal::Const(k) => {
                        self.load_decider(eg, &vec![vec![]], out_const(x, k), None, format!("{name} (conditional load)"));
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
        self.hold(distribute(&[], &hold), x, name);
        if init != 0 {
            self.shared(vec![c(self.st, CmpOp::Ne, 0)], out_const(x, init), format!("{name} (initial value {init})"));
        }
        Ok(())
    }

    /// A sample register: copies `raw` into a new signal whenever `en` fires.
    pub(super) fn sample(&mut self, raw: Sig, en: Sig, what: &str) -> Result<Sig, Diag> {
        let smp = self.alloc()?;
        self.hold(vec![c(en, CmpOp::Eq, 0), c(self.run, CmpOp::Ne, 0)], smp, &format!("sample of {what}"));
        self.core(arith(Operand::Sig(raw), ArOp::Mul, Operand::Sig(en), smp), format!("sample of {what} (load)"));
        Ok(smp)
    }

    /// Staged samples: `sigs` arrive on private red wire `net` (instead of the bus) and are
    /// all loaded by one `each × en` whenever `en` fires, under their own signals.
    pub(super) fn staged_samples(&mut self, net: usize, sigs: &[Sig], en: Sig, what: &str) {
        for &s in sigs {
            self.hold(vec![c(en, CmpOp::Eq, 0), c(self.run, CmpOp::Ne, 0)], s, &format!("sample of {what}"));
        }
        let each = self.each;
        let load = Arith { first: Operand::Sig(each), first_nets: Nets::RED, second: Operand::Sig(en), second_nets: Nets::GREEN, op: ArOp::Mul, out: each };
        let id = self.loose(Kind::Arith(load), format!("samples of {what}: inputs (load)"));
        self.nets[net].members.push((id, Conn::InRed));
        self.on_bus_in(id);
        self.nets[0].members.push((id, Conn::OutGreen));
    }

    /// A bundle register: like [`Cg::register`], but the value is a whole bundle on its own
    /// wire. The hold decider copies everything from that wire while no load fires; loads
    /// multiply the new bundle by their enable pulse.
    pub(super) fn bregister(&mut self, x: BRef, init: &[(Sig, i32)], writers: &[Writer], name: &str) -> Result<(), Diag> {
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
                    let eg = self.load_condition(w, &l.guard, format!("{name} (load condition)"))?;
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
    pub(super) fn bsample(&mut self, raw: BRef, en: Sig, what: &str) -> BRef {
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
    pub(super) fn sample_ref(&mut self, raw: Ref, en: Sig, what: &str) -> Result<Ref, Diag> {
        Ok(match raw {
            Ref::Op(Operand::Sig(s)) => Ref::Op(Operand::Sig(self.sample(s, en, what)?)),
            Ref::Bun(b) => Ref::Bun(self.bsample(b, en, what)),
            Ref::Op(Operand::Const(_)) => unreachable!("sampling a constant"),
        })
    }
}

/// One register's plan in one writer, for [`Cg::stage_loads`]. `key` names the plan, `writer`
/// its commit (a step, or the block); `incs` marks increments.
pub(super) struct StageIn<'a> {
    pub(super) key: usize,
    pub(super) writer: usize,
    pub(super) x: Sig,
    pub(super) plan: &'a mut WriterPlan,
    pub(super) incs: &'a [bool],
}

/// Staged loads: (plan key, load) → the value, its register and its staging wire; and the
/// other loads whose guards test a staged value: (plan key, load) → the value.
#[derive(Default)]
pub(super) struct Staging {
    loads: HashMap<(usize, usize), (V, Sig, usize)>,
    reads: HashMap<(usize, usize), V>,
}

impl Staging {
    /// What [`Cg::logic`] is asked to write: each value under its register's signal onto
    /// its wire.
    pub(super) fn vals(&self) -> HashMap<V, (Sig, usize)> {
        self.loads.values().map(|&(v, x, net)| (v, (x, net))).collect()
    }

    /// Keeps the loads whose values `logic()` did stage (`vals` as it left them).
    pub(super) fn settle(&mut self, vals: &HashMap<V, (Sig, usize)>) {
        self.loads.retain(|_, (v, _, _)| vals.contains_key(v));
        self.reads.retain(|_, v| vals.contains_key(v));
    }

    /// `Writer::stage` for plan `key`, with `n` loads.
    pub(super) fn of(&self, key: usize, n: usize) -> Vec<Option<LoadStage>> {
        let wire = |v: V| self.loads.values().find(|s| s.0 == v).map(|s| s.2);
        (0..n)
            .map(|l| match (self.loads.get(&(key, l)), self.reads.get(&(key, l))) {
                (Some(&(v, _, wire)), _) => Some(LoadStage { v, wire, copy: true }),
                (_, Some(&v)) => wire(v).map(|wire| LoadStage { v, wire, copy: false }),
                _ => None,
            })
            .collect()
    }
}

impl Cg {
    /// Chooses the staged loads of a block or process (see the module doc) before its
    /// `logic()`. A value qualifies when nothing else reads it: no other node, and no root
    /// (`roots` counts every use outside the graph) but its own load and the guards of its
    /// register's loads in the same writer. Guarded loads that replace the value become
    /// direct (`plan.keep` grows to cover them, if it stays small; the hold reads it from the
    /// bus, so it mustn't test the value). A guard testing it must be read on the commit tick
    /// from the wire: only the staged load itself, direct constant loads and constant
    /// increments, each testing one staged value. Loads of one writer under the same guard go
    /// onto one wire (one decider loads them all); a wire carries each register's signal at
    /// most once, and an unconditional load alone keeps its `value × en` (no cheaper staged).
    pub(super) fn stage_loads(&mut self, g: &Graph, roots: &[V], plans: Vec<StageIn>) -> Staging {
        let mut count: HashMap<V, usize> = HashMap::new();
        for &r in roots {
            *count.entry(r).or_default() += 1;
        }
        let used: HashSet<V> = g.reachable(roots).into_iter().flat_map(|v| g.operands(v)).collect();
        let stageable = |v: V| {
            !used.contains(&v) && matches!(g.op(v), Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) | Op::Sel(_) | Op::BGet(..) | Op::BTotal(_) | Op::BCount(_))
        };
        let mut out = Staging::default();
        // By (writer, guard): the loads (register, plan key, load index, value).
        type Group = ((usize, crate::ir::Dnf), Vec<(Sig, usize, usize, V)>);
        let mut groups: Vec<Group> = Vec::new();
        for p in plans {
            let loads = p.plan.loads.clone();
            let n = loads.len();
            let inc = |l: usize| p.incs.get(l).copied().unwrap_or(false);
            let node = |l: usize| match loads[l].val {
                LoadVal::Node(v) => Some(v),
                LoadVal::Const(_) => None,
            };
            let mentions = |d: &crate::ir::Dnf, v: V| crate::ir::dnf_operands(d).any(|o| o == v);
            let ops = p.plan.operands();
            // Values used only here, as this one load's value.
            let mut ok: Vec<usize> = (0..n)
                .filter(|&l| {
                    node(l).is_some_and(|v| {
                        stageable(v) && count.get(&v) == Some(&ops.iter().filter(|&&o| o == v).count()) && (0..n).all(|m| m == l || node(m) != Some(v))
                    })
                })
                .collect();
            let readers = |l: usize| -> Vec<usize> { (0..n).filter(|&m| m != l && mentions(&loads[m].guard, node(l).unwrap())).collect() };
            // Other loads testing the value: constants, each testing one candidate.
            let mut tested: HashSet<usize> = HashSet::new();
            ok.retain(|&l| readers(l).iter().all(|&m| node(m).is_none() && !tested.contains(&m)) && readers(l).iter().all(|&m| tested.insert(m)));
            // Direct from now on: guarded candidates that replace the value, and guarded
            // constant loads testing a candidate.
            let mut direct: Vec<usize> = ok.iter().copied().filter(|&l| !inc(l) && !is_true(&loads[l].guard)).collect();
            direct.extend(ok.iter().flat_map(|&l| readers(l)).filter(|&m| !inc(m) && !loads[m].direct));
            let keep = if direct.is_empty() {
                Some(p.plan.keep.clone())
            } else {
                let guards: Vec<&crate::ir::Dnf> = loads.iter().enumerate().filter(|(l, ld)| ld.direct || direct.contains(l)).map(|(_, ld)| &ld.guard).collect();
                keep_of(&guards).map(Some)
            };
            match keep {
                Some(k) => {
                    for &l in &direct {
                        p.plan.loads[l].direct = true;
                    }
                    p.plan.keep = k;
                }
                None => {
                    // Too big a hold condition: only what needs no new direct loads.
                    ok.retain(|&l| (inc(l) || is_true(&loads[l].guard)) && readers(l).iter().all(|&m| inc(m) || loads[m].direct));
                }
            }
            if let Some(k) = &p.plan.keep {
                ok.retain(|&l| !mentions(k, node(l).unwrap()));
            }
            for l in ok {
                let v = node(l).unwrap();
                for m in readers(l) {
                    out.reads.insert((p.key, m), v);
                }
                let key = (p.writer, loads[l].guard.clone());
                match groups.iter_mut().find(|(k, _)| *k == key) {
                    Some((_, m)) => m.push((p.x, p.key, l, v)),
                    None => groups.push((key, vec![(p.x, p.key, l, v)])),
                }
            }
        }
        let mut wires: Vec<(usize, Vec<Sig>)> = Vec::new();
        for ((_, guard), members) in groups {
            if is_true(&guard) && members.len() == 1 {
                continue;
            }
            let w = match wires.iter().position(|(_, sigs)| members.iter().all(|m| !sigs.contains(&m.0))) {
                Some(w) => w,
                None => {
                    self.nets.push(NetSpec { red: true, members: Vec::new() });
                    wires.push((self.nets.len() - 1, Vec::new()));
                    wires.len() - 1
                }
            };
            for (x, key, l, v) in members {
                wires[w].1.push(x);
                out.loads.insert((key, l), (v, x, wires[w].0));
            }
        }
        out
    }
}

/// Increments: a load of `own + a` (or `own ± k`) can add `a` to a register that keeps
/// holding, instead of replacing its value: no adder, and the hold doesn't stop for it (when
/// every load is one, it shares the program-wide `[ST=0 ∧ RUN≠0]` hold). Rewrites such loads
/// of `plan` in place; the result says which loads are now increments. `own` is the
/// register's own value in `g`.
pub(super) fn increments(g: &Graph, own: Option<V>, plan: &mut WriterPlan) -> Vec<bool> {
    let Some(own) = own else { return vec![false; plan.loads.len()] };
    let mut out = Vec::new();
    for l in &mut plan.loads {
        let LoadVal::Node(v) = l.val else {
            out.push(false);
            continue;
        };
        let step = match *g.op(v) {
            Op::Ar(ArOp::Add, a, b) if a == own => Some((b, 1)),
            Op::Ar(ArOp::Add, a, b) if b == own => Some((a, 1)),
            Op::Ar(ArOp::Sub, a, b) if a == own => Some((b, -1)),
            _ => None,
        };
        let val = match step {
            Some((a, sign)) => match g.as_const(a) {
                Some(k) => k.checked_mul(sign).map(LoadVal::Const),
                None if sign == 1 => Some(LoadVal::Node(a)),
                None => None,
            },
            None => None,
        };
        out.push(val.is_some());
        if let Some(val) = val {
            l.val = val;
            l.direct = false;
        }
    }
    out
}

/// The node of state `si`'s own value in a graph whose sources are `srcs`.
pub(super) fn own_node(g: &Graph, srcs: &[SrcKind], si: usize) -> Option<V> {
    let s = srcs.iter().position(|k| *k == SrcKind::Own(si))?;
    g.nodes.iter().position(|o| *o == Op::Src(s as u32)).map(|v| v as V)
}

/// One writer of a register, as seen by codegen.
pub(super) struct Writer<'a> {
    pub(super) en: Sig,
    pub(super) prefix: Vec<Cond>,
    pub(super) plan: &'a WriterPlan,
    /// Where a load's value is.
    pub(super) val: &'a dyn Fn(V) -> Ref,
    /// Conditions read on the commit tick.
    pub(super) lit: &'a dyn Fn(&Lit) -> Cond,
    /// Conditions read one tick earlier, by enable deciders.
    pub(super) lit_eg: &'a dyn Fn(&Lit) -> Cond,
    /// Per load: the staged value it copies or tests ([`Cg::stage_loads`]).
    pub(super) stage: Vec<Option<LoadStage>>,
}

/// A load's part in staging: it copies staged value `v` from `wire` (`copy`), or its guard
/// only tests it there.
#[derive(Copy, Clone)]
pub(super) struct LoadStage {
    v: V,
    wire: usize,
    copy: bool,
}

/// A load's guard as conditions read on the commit tick, from the bus, except a staged
/// value: register `x`'s signal on the red staging wire.
fn guard_conds(w: &Writer, guard: &crate::ir::Dnf, x: Sig, stage: Option<LoadStage>) -> CDnf {
    let side = |o: V| match stage {
        Some(s) if s.v == o => (Operand::Sig(x), Nets::RED),
        _ => ((w.val)(o).op(), Nets::GREEN),
    };
    guard
        .iter()
        .map(|t| {
            t.iter()
                .map(|l| match stage {
                    Some(s) if l.a == s.v || l.b == s.v => {
                        let ((first, first_nets), (second, second_nets)) = (side(l.a), side(l.b));
                        let Operand::Sig(first) = first else { unreachable!("a literal's first operand is a signal") };
                        Cond { first, first_nets, second, second_nets, cmp: l.op, and: true }
                    }
                    _ => green((w.lit)(l)),
                })
                .collect()
        })
        .collect()
}

/// `x += w` every tick: the hold decider copies x from a private red loop on which `w`
/// (renamed to x's signal) is also summed.
#[allow(clippy::too_many_arguments)]
pub(super) fn accumulator(
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
