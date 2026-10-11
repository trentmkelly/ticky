//! State-holding machinery: registers (hold decider + guarded loads, scalar and bundle),
//! sample registers, the step-timer style counter and the every-tick accumulator.
//!
//! Deciders that differ only in their outputs are built once with all the outputs
//! ([`Cg::shared`]): the holds of registers held under the same conditions (`[conds] → x
//! copy, y copy, …`), and every initial value (`[ST≠0] → x = 1, y = 5, …`).

use ticky_factorio::*;
use ticky_syntax::Diag;

use super::*;
use crate::fuse::{is_true, LoadVal, WriterPlan};
use crate::ir::{Lit, V};

/// A decider waiting for others with the same conditions.
pub(super) struct Pending {
    conds: Vec<Cond>,
    outs: Vec<DOut>,
    descs: Vec<String>,
}

impl Cg {
    /// A decider `[conds] → out`, merged with every other one of the same conditions in this
    /// block or process (program-wide when the conditions only test RUN, RP and ST). The
    /// outputs must be on distinct signals. Built by [`Cg::flush_shared`].
    pub(super) fn shared(&mut self, conds: Vec<Cond>, out: DOut, desc: impl Into<String>) {
        let desc = desc.into();
        match self.pending.iter_mut().find(|p| p.conds == conds) {
            Some(p) => {
                p.outs.push(out);
                p.descs.push(desc);
            }
            None => self.pending.push(Pending { conds, outs: vec![out], descs: vec![desc] }),
        }
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
        for p in now {
            self.core(dec(p.conds, p.outs), p.descs.join("; "));
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
