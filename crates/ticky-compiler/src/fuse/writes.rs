//! Combining writes into a bundle ([`Fuser::combine_writes`], from `rebuild` of a `Bun`):
//! several `Set`s on one base share one "take the old values out" combinator, and signals
//! getting the same value share a term; constants under conditions become deciders
//! ([`Fuser::const_arms`]).

use ticky_factorio::ArOp;

use super::*;
use crate::ir::{BTerm, Lit, Op, V};

impl Fuser<'_> {
    /// A rebuilt condition value `x` (constants under conditions) written on signals `sigs`:
    /// a decider per arm outputting the constant on all of them.
    pub(super) fn const_arms(&mut self, x: V, sigs: &[ticky_factorio::Sig]) -> Option<BTerm> {
        let arms = match self.g.op(x).clone() {
            Op::Dec(arms) => arms,
            Op::Cmp(op, a, b) if self.g.as_const(a).is_none() => vec![(vec![vec![Lit { op, a, b }]], 1)],
            _ => return None,
        };
        Some(BTerm::Dec(arms.into_iter().map(|(d, k)| (d, crate::ir::normalize(sigs.iter().map(|s| (*s, k))))).collect()))
    }

    /// Several signals set on one bundle (`b0` copied, then `x_i - b0[s_i]` on each `s_i`):
    /// one combinator takes the old values out (`b0 × (-1 on every s_i)`), and the signals that
    /// get the same value share a term (constants, a decider per condition, or a table of
    /// ones times the value). Also `ones × condition` as deciders.
    pub(super) fn combine_writes(&mut self, terms: Vec<BTerm>) -> Vec<BTerm> {
        let mut out = Vec::new();
        // base → [(signal, value)]
        let mut sets: Vec<(V, Vec<(ticky_factorio::Sig, V)>)> = Vec::new();
        for t in terms {
            match t {
                BTerm::Set(b0, s, x) => match sets.iter_mut().find(|(b, _)| *b == b0) {
                    Some((_, v)) => v.push((s, x)),
                    None => sets.push((b0, vec![(s, x)])),
                },
                BTerm::Map(ArOp::Mul, ones, x) if self.g.as_bconst(ones).is_some_and(|b| b.iter().all(|(_, k)| *k == 1)) => {
                    let sigs: Vec<_> = self.g.as_bconst(ones).unwrap().iter().map(|(s, _)| *s).collect();
                    match self.const_arms(x, &sigs) {
                        Some(d) => out.push(d),
                        None => out.push(BTerm::Map(ArOp::Mul, ones, x)),
                    }
                }
                t => out.push(t),
            }
        }
        for (b0, writes) in sets {
            if writes.len() == 1 {
                let (s, x) = writes[0];
                out.push(BTerm::Set(b0, s, x));
                continue;
            }
            let neg = self.g.bconst(writes.iter().map(|(s, _)| (*s, -1)));
            out.push(BTerm::Zip(ArOp::Mul, b0, neg));
            let mut konst = Vec::new();
            let mut groups: Vec<(V, Vec<ticky_factorio::Sig>)> = Vec::new();
            for (s, x) in writes {
                match self.g.as_const(x) {
                    Some(k) => konst.push((s, k)),
                    None => match groups.iter_mut().find(|(v, _)| *v == x) {
                        Some((_, ss)) => ss.push(s),
                        None => groups.push((x, vec![s])),
                    },
                }
            }
            out.push(BTerm::K(crate::ir::normalize(konst)));
            for (x, sigs) in groups {
                if let Some(d) = self.const_arms(x, &sigs) {
                    out.push(d);
                } else if let ([s], Op::Ar(op, a, b)) = (sigs.as_slice(), self.g.op(x).clone()) {
                    out.push(BTerm::Ar(op, a, b, *s));
                } else if let [s] = sigs.as_slice() {
                    out.push(BTerm::One(*s, x));
                } else {
                    let ones = self.g.bconst(sigs.iter().map(|s| (*s, 1)));
                    out.push(BTerm::Map(ArOp::Mul, ones, x));
                }
            }
        }
        out
    }
}
