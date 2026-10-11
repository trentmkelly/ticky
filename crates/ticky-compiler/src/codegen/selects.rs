//! Select stages for [`Cg::logic`](super::Cg): a select (`Mux`/`Sel`), together with the
//! selects and conditions only it uses, becomes one stage of deciders writing the select's
//! signal: one decider per distinct output (a constant, or a value passed through from a
//! private wire), each testing its whole condition itself.
//!
//! * **Inlined conditions.** A comparison (or one-term condition) used only to choose arms
//!   isn't built: the arms' deciders test it (`K if x > 5 else …` is one decider).
//! * **Passes.** An arm value used only by the stage (as the arm, or inside its conditions)
//!   is computed onto the select's own signal on a private red wire, and the arm's decider
//!   copies it from there (`DOut copy, nets RED`). So `max(x, K)` is two deciders reading
//!   `x` off the wire (`x ≥ K → copy`, `x < K → K`) and `x if x > 0 else 0` one.
//! * **Absorbed selects.** A select used only by the stage, as an arm or inside its
//!   conditions, is flattened into it: arms nest (`c ∧ d → …`), and a condition reading it
//!   is split by its arms (`min(max(x, lo), hi)`: `x > hi → hi`, `x < lo → lo`, else `x`).
//! * **More than one pass.** The first pass shares the cluster's wire; each further one gets
//!   a wire of its own, and every other value its deciders read moves to the bus (a decider
//!   has one red input).
//!
//! Arms are mutually exclusive, so deciders with the same output merge (their conditions
//! OR'd) and the stage's value is their sum.

use std::collections::{HashMap, HashSet};

use ticky_factorio::CmpOp;

use crate::ir::{Graph, Op, V};

/// A condition operand: a value, or a constant (a constant arm substituted for a select).
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub(super) enum Opd {
    V(V),
    K(i32),
}

#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub(super) struct SLit {
    pub op: CmpOp,
    pub a: Opd,
    pub b: Opd,
}

/// OR of AND-terms. `[]` is false; terms are never empty (see `simplify`).
pub(super) type SDnf = Vec<Vec<SLit>>;

/// What a stage's combinator writes when its condition holds.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
pub(super) enum Out {
    K(i32),
    /// The value, from the private wire it was computed onto (under the select's signal).
    Pass(V),
    /// `value * condition` (an arithmetic combinator): a top-level arm whose value is needed
    /// elsewhere too.
    Mul(V, V),
}

pub(super) struct Stage {
    /// One combinator each.
    pub deciders: Vec<(SDnf, Out)>,
    /// Passed values: the first on the cluster's wire, each other on a wire of its own.
    pub passes: Vec<V>,
}

impl Stage {
    /// The values a combinator of the stage reads.
    pub fn reads(dnf: &SDnf, out: &Out) -> Vec<V> {
        let mut r: Vec<V> = dnf.iter().flatten().flat_map(|l| [l.a, l.b]).filter_map(|o| if let Opd::V(v) = o { Some(v) } else { None }).collect();
        match *out {
            Out::K(_) => {}
            Out::Pass(x) => r.push(x),
            Out::Mul(x, c) => r.extend([x, c]),
        }
        r.sort_unstable();
        r.dedup();
        r
    }

    pub fn all_reads(&self) -> Vec<V> {
        let mut r: Vec<V> = self.deciders.iter().flat_map(|(d, o)| Stage::reads(d, o)).collect();
        r.sort_unstable();
        r.dedup();
        r
    }
}

#[derive(Default)]
pub(super) struct Plan {
    /// By root select. Every select that isn't absorbed is a root.
    pub stages: HashMap<V, Stage>,
    /// Selects flattened into another's stage: not built.
    pub absorbed: HashSet<V>,
    /// Conditions tested by the deciders using them: not built.
    pub inline_cond: HashSet<V>,
    /// Values read by a decider whose red input is a further pass's own wire: on the bus.
    pub force_bus: HashSet<V>,
}

impl Plan {
    pub fn has_pass(&self, v: V) -> bool {
        self.stages.get(&v).is_some_and(|s| !s.passes.is_empty())
    }
}

/// Something that made a plan fail; planning again without it always gets further.
#[derive(Copy, Clone, PartialEq, Eq, Hash, Debug)]
enum Ban {
    Absorb(V),
    Pass(V),
    Inline(V),
}

/// Most arms a stage may grow to while flattening, and literals per decider.
const MAX_ARMS: usize = 64;
const MAX_LITS: usize = 48;

pub(super) fn plan(g: &Graph, producers: &[V], is_root: &HashSet<V>, pre: &HashMap<V, Vec<V>>) -> Plan {
    let mut bans = HashSet::new();
    loop {
        match try_plan(g, producers, is_root, pre, &bans) {
            Ok(p) => return p,
            Err(b) => assert!(bans.insert(b), "select planning repeated {b:?}"),
        }
    }
}

fn is_select(g: &Graph, v: V) -> bool {
    matches!(g.op(v), Op::Mux { .. } | Op::Sel(_))
}

fn is_scalar_op(g: &Graph, v: V) -> bool {
    matches!(g.op(v), Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) | Op::Sel(_))
}

/// A condition that can be written as decider literals.
fn boolean(g: &Graph, c: V) -> bool {
    match g.op(c) {
        Op::Cmp(_, a, _) => g.as_const(*a).is_none(),
        Op::Dec(arms) => arms.len() == 1 && arms[0].1 == 1,
        _ => false,
    }
}

/// A select's arms as (condition, value); for a `Mux` both, zero or not.
fn arms_of(g: &Graph, v: V) -> Vec<(V, V)> {
    match g.op(v) {
        Op::Mux { t, f, a, b } => vec![(*t, *a), (*f, *b)],
        Op::Sel(arms) => arms.clone(),
        _ => vec![],
    }
}

/// Arms that contribute (value ≠ 0): their conditions are the select's operands.
fn live_arms(g: &Graph, v: V) -> Vec<(V, V)> {
    arms_of(g, v).into_iter().filter(|(_, x)| g.as_const(*x) != Some(0)).collect()
}

fn opd(g: &Graph, v: V) -> Opd {
    match g.as_const(v) {
        Some(k) => Opd::K(k),
        None => Opd::V(v),
    }
}

/// The literals of an inlinable condition.
fn lits(g: &Graph, c: V) -> SDnf {
    match g.op(c) {
        Op::Cmp(op, a, b) => vec![vec![SLit { op: *op, a: opd(g, *a), b: opd(g, *b) }]],
        Op::Dec(arms) => arms[0].0.iter().map(|t| t.iter().map(|l| SLit { op: l.op, a: opd(g, l.a), b: opd(g, l.b) }).collect()).collect(),
        _ => unreachable!("not an inlinable condition"),
    }
}

/// Conjunction.
fn and(x: &SDnf, y: &SDnf) -> SDnf {
    let mut out = Vec::new();
    for a in x {
        for b in y {
            out.push(a.iter().chain(b.iter()).copied().collect());
        }
    }
    out
}

/// Negation, if it stays small.
fn not(g: &Graph, d: &SDnf) -> Option<SDnf> {
    let mut out: SDnf = vec![vec![]];
    for t in d {
        let alts: SDnf = t.iter().map(|l| vec![SLit { op: l.op.negate(), ..*l }]).collect();
        out = simplify(g, and(&out, &alts))?;
        if out.len() > MAX_ARMS {
            return None;
        }
    }
    Some(out)
}

/// Folds constant literals, tightens comparisons of one value with constants to its known
/// range (dropping implied ones and false terms) and removes duplicates. A term left with no
/// literal (always true) keeps one of its own, as deciders need one; `None` if it had none
/// reading a value.
fn simplify(g: &Graph, d: SDnf) -> Option<SDnf> {
    const MIN: i64 = i32::MIN as i64;
    const MAX: i64 = i32::MAX as i64;
    let mut out: SDnf = Vec::new();
    'terms: for t in d {
        let keep = t.iter().find_map(|l| match (l.a, l.b) {
            (Opd::V(_), Opd::K(_)) => Some(*l),
            (Opd::K(_), Opd::V(_)) => Some(SLit { op: l.op.flip(), a: l.b, b: l.a }),
            _ => None,
        });
        // Per value: allowed interval and excluded points; other literals as they are.
        let mut bounds: Vec<(V, i64, i64, Vec<i64>)> = Vec::new();
        let mut rest: Vec<SLit> = Vec::new();
        for l in t {
            let (v, op, k) = match (l.a, l.b) {
                (Opd::K(x), Opd::K(y)) => {
                    if l.op.apply(x, y) {
                        continue;
                    }
                    continue 'terms;
                }
                (Opd::V(v), Opd::K(k)) => (v, l.op, k as i64),
                (Opd::K(k), Opd::V(v)) => (v, l.op.flip(), k as i64),
                (Opd::V(x), Opd::V(y)) if x == y => {
                    if matches!(l.op, CmpOp::Eq | CmpOp::Le | CmpOp::Ge) {
                        continue;
                    }
                    continue 'terms;
                }
                _ => {
                    if !rest.contains(&l) {
                        rest.push(l);
                    }
                    continue;
                }
            };
            let i = match bounds.iter().position(|b| b.0 == v) {
                Some(i) => i,
                None => {
                    let iv = g.iv(v);
                    bounds.push((v, iv.lo.max(MIN), iv.hi.min(MAX), Vec::new()));
                    bounds.len() - 1
                }
            };
            let b = &mut bounds[i];
            match op {
                CmpOp::Lt => b.2 = b.2.min(k - 1),
                CmpOp::Le => b.2 = b.2.min(k),
                CmpOp::Gt => b.1 = b.1.max(k + 1),
                CmpOp::Ge => b.1 = b.1.max(k),
                CmpOp::Eq => {
                    b.1 = b.1.max(k);
                    b.2 = b.2.min(k);
                }
                CmpOp::Ne => b.3.push(k),
            }
        }
        let mut lits: Vec<SLit> = Vec::new();
        for (v, lo, hi, ne) in bounds {
            if lo > hi {
                continue 'terms;
            }
            let iv = g.iv(v);
            let k = |x: i64| Opd::K(x as i32);
            if lo == hi && (lo > iv.lo || hi < iv.hi) {
                if ne.contains(&lo) {
                    continue 'terms;
                }
                lits.push(SLit { op: CmpOp::Eq, a: Opd::V(v), b: k(lo) });
                continue;
            }
            if lo > iv.lo {
                lits.push(SLit { op: CmpOp::Ge, a: Opd::V(v), b: k(lo) });
            }
            if hi < iv.hi {
                lits.push(SLit { op: CmpOp::Le, a: Opd::V(v), b: k(hi) });
            }
            let mut ne: Vec<i64> = ne.into_iter().filter(|x| (lo..=hi).contains(x)).collect();
            ne.sort_unstable();
            ne.dedup();
            if lo == hi && ne.contains(&lo) {
                continue 'terms;
            }
            lits.extend(ne.into_iter().map(|x| SLit { op: CmpOp::Ne, a: Opd::V(v), b: k(x) }));
        }
        lits.extend(rest);
        if lits.is_empty() {
            lits.push(keep?);
        }
        if !out.contains(&lits) {
            out.push(lits);
        }
    }
    Some(out)
}

/// Replaces value `n` by `by` in every literal.
fn subst(d: &SDnf, n: V, by: Opd) -> SDnf {
    let s = |o: Opd| if o == Opd::V(n) { by } else { o };
    d.iter().map(|t| t.iter().map(|l| SLit { op: l.op, a: s(l.a), b: s(l.b) }).collect()).collect()
}

struct Ctx<'a> {
    g: &'a Graph,
    is_root: &'a HashSet<V>,
    pre: &'a HashMap<V, Vec<V>>,
    bans: &'a HashSet<Ban>,
}

impl Ctx<'_> {
    fn users(&self, v: V) -> &[V] {
        self.pre.get(&v).map(|u| u.as_slice()).unwrap_or(&[])
    }

    /// The conditions of `members` that only they use, only as conditions.
    fn stage_conds(&self, members: &HashSet<V>) -> HashSet<V> {
        let g = self.g;
        let values: HashSet<V> = members.iter().flat_map(|&u| arms_of(g, u).into_iter().map(|(_, x)| x)).collect();
        members
            .iter()
            .flat_map(|&u| live_arms(g, u).into_iter().map(|(c, _)| c))
            .filter(|&c| {
                boolean(g, c) && !self.is_root.contains(&c) && !self.bans.contains(&Ban::Inline(c)) && !values.contains(&c) && self.users(c).iter().all(|u| members.contains(u))
            })
            .collect()
    }

    /// The selects flattened into `m`'s stage, and the stage's own conditions.
    fn absorb(&self, m: V, taken: &HashMap<V, V>) -> (Vec<V>, HashSet<V>) {
        let g = self.g;
        let mut a: Vec<V> = Vec::new();
        loop {
            let members: HashSet<V> = std::iter::once(m).chain(a.iter().copied()).collect();
            let conds = self.stage_conds(&members);
            let inside = |u: &V| members.contains(u) || conds.contains(u);
            // Selects read by the stage's conditions (split by their arms; needs a `Mux`,
            // whose arms cover every case) or used as its arms (`Mux` or `Sel`).
            let read: HashSet<V> = conds.iter().flat_map(|&c| lits(g, c).into_iter().flatten().flat_map(|l| [l.a, l.b])).filter_map(|o| if let Opd::V(v) = o { Some(v) } else { None }).collect();
            let arm_vals: Vec<V> = members.iter().flat_map(|&u| live_arms(g, u).into_iter().map(|(_, x)| x)).collect();
            let guards: HashSet<V> = members.iter().flat_map(|&u| live_arms(g, u).into_iter().map(|(c, _)| c)).collect();
            let mut cands: Vec<V> = read.iter().copied().chain(arm_vals.iter().copied()).filter(|&n| is_select(g, n)).collect();
            cands.sort_unstable();
            cands.dedup();
            let next = cands.into_iter().rev().find(|&n| {
                !members.contains(&n)
                    && !taken.contains_key(&n)
                    && !self.is_root.contains(&n)
                    && !self.bans.contains(&Ban::Absorb(n))
                    && !guards.contains(&n)
                    && self.users(n).iter().all(inside)
                    && (matches!(g.op(n), Op::Mux { .. }) || !read.contains(&n))
            });
            match next {
                Some(n) => a.push(n),
                None => return (a, conds),
            }
        }
    }

    /// Arms of an absorbed select as (condition, value), covering every case for a `Mux`.
    fn sub_arms(&self, n: V, inl: &dyn Fn(V) -> bool) -> Option<Vec<(SDnf, V)>> {
        let g = self.g;
        let guard = |c: V| if inl(c) { lits(g, c) } else { vec![vec![SLit { op: CmpOp::Ne, a: Opd::V(c), b: Opd::K(0) }]] };
        Some(match *g.op(n) {
            Op::Mux { t, f, a, b } => {
                let zero = |x: V| g.as_const(x) == Some(0);
                if !zero(a) && !zero(b) {
                    vec![(guard(t), a), (guard(f), b)]
                } else if !zero(a) {
                    let gt = guard(t);
                    let nt = not(g, &gt)?;
                    vec![(gt, a), (nt, b)]
                } else {
                    let gf = guard(f);
                    let nf = not(g, &gf)?;
                    vec![(nf, a), (gf, b)]
                }
            }
            _ => live_arms(g, n).into_iter().map(|(c, x)| (guard(c), x)).collect(),
        })
    }

    /// The stage's arms, flattened: (condition, value, the select whose arm or condition it
    /// came from if not `m`'s own, `m`'s condition if it is).
    fn flatten(&self, m: V, a: &[V], inl: &dyn Fn(V) -> bool) -> Result<Vec<(SDnf, V, Result<V, V>)>, Ban> {
        let g = self.g;
        let absorbed: HashSet<V> = a.iter().copied().collect();
        let ban_last = || Ban::Absorb(*a.last().expect("flattening without absorbed selects"));
        let guard = |c: V| if inl(c) { lits(g, c) } else { vec![vec![SLit { op: CmpOp::Ne, a: Opd::V(c), b: Opd::K(0) }]] };
        let mut work: Vec<(SDnf, V, Result<V, V>)> = live_arms(g, m).into_iter().map(|(c, x)| (guard(c), x, Err(c))).collect();
        let mut done = Vec::new();
        while let Some((d, x, from)) = work.pop() {
            let d = simplify(g, d).ok_or(match from {
                Ok(n) => Ban::Absorb(n),
                Err(c) => Ban::Inline(c),
            })?;
            if d.is_empty() || g.as_const(x) == Some(0) {
                continue;
            }
            if !a.is_empty() && work.len() + done.len() > MAX_ARMS {
                return Err(ban_last());
            }
            // A condition reading an absorbed select: one arm per arm of it.
            let read = d.iter().flatten().flat_map(|l| [l.a, l.b]).find_map(|o| match o {
                Opd::V(v) if absorbed.contains(&v) => Some(v),
                _ => None,
            });
            if let Some(n) = read {
                for (dn, y) in self.sub_arms(n, inl).ok_or(Ban::Absorb(n))? {
                    work.push((and(&subst(&d, n, opd(g, y)), &dn), x, Ok(n)));
                }
                continue;
            }
            if absorbed.contains(&x) {
                for (dn, y) in self.sub_arms(x, inl).ok_or(Ban::Absorb(x))? {
                    work.push((and(&d, &dn), y, Ok(x)));
                }
                continue;
            }
            done.push((d, x, from));
        }
        done.reverse();
        Ok(done)
    }

    /// `x` can be computed onto the stage's private wire: only the stage uses it. (A select that
/// isn't flattened can be too, if it passes nothing itself; checked once all are planned.)
    fn passable(&self, x: V, inside: &dyn Fn(&V) -> bool, guards: &HashSet<V>) -> bool {
        let g = self.g;
        g.as_const(x).is_none()
            && !self.bans.contains(&Ban::Pass(x))
            && !self.is_root.contains(&x)
            && !guards.contains(&x)
            && (is_scalar_op(g, x) || matches!(g.op(x), Op::BGet(..) | Op::BTotal(_) | Op::BCount(_)))
            && !self.users(x).is_empty()
            && self.users(x).iter().all(inside)
    }
}

/// What each flattened arm writes: its constant, its value passed through (if in `ok`), or
/// its value times its (top-level, built) condition.
fn outputs(g: &Graph, arms: Vec<(SDnf, V, Result<V, V>)>, ok: &HashSet<V>, inl: &dyn Fn(V) -> bool) -> Result<Vec<(SDnf, Out)>, Ban> {
    arms.into_iter()
        .map(|(d, x, from)| {
            let out = match g.as_const(x) {
                Some(k) => Out::K(k),
                None if ok.contains(&x) => Out::Pass(x),
                None => match from {
                    Err(c) if inl(c) => return Err(Ban::Inline(c)),
                    Err(c) => Out::Mul(x, c),
                    Ok(n) => return Err(Ban::Absorb(n)),
                },
            };
            Ok((d, out))
        })
        .collect()
}

fn try_plan(g: &Graph, producers: &[V], is_root: &HashSet<V>, pre: &HashMap<V, Vec<V>>, bans: &HashSet<Ban>) -> Result<Plan, Ban> {
    let cx = Ctx { g, is_root, pre, bans };
    // Outermost selects first (users come after their operands), so each absorbs what it can.
    let mut taken: HashMap<V, V> = HashMap::new();
    let mut roots: Vec<(V, Vec<V>, HashSet<V>)> = Vec::new();
    for &m in producers.iter().rev() {
        if !is_select(g, m) || taken.contains_key(&m) {
            continue;
        }
        let (a, conds) = cx.absorb(m, &taken);
        for &n in &a {
            taken.insert(n, m);
        }
        roots.push((m, a, conds));
    }
    // Arm outputs, with each stage's own conditions inlined.
    let mut pass_ok: HashMap<V, HashSet<V>> = HashMap::new();
    let mut mul_guards: HashSet<V> = HashSet::new();
    let mut inline_cond: HashSet<V> = HashSet::new();
    for (m, a, conds) in &roots {
        let members: HashSet<V> = std::iter::once(*m).chain(a.iter().copied()).collect();
        let guards: HashSet<V> = members.iter().flat_map(|&u| arms_of(g, u).into_iter().map(|(c, _)| c)).collect();
        let inside = |u: &V| members.contains(u) || conds.contains(u);
        let arms = cx.flatten(*m, a, &|c| conds.contains(&c))?;
        let ok: HashSet<V> = arms.iter().map(|(_, x, _)| *x).filter(|&x| cx.passable(x, &inside, &guards)).collect();
        for (_, out) in outputs(g, arms, &ok, &|c| conds.contains(&c))? {
            if let Out::Mul(_, c) = out {
                mul_guards.insert(c);
            }
        }
        inline_cond.extend(conds.iter().copied());
        pass_ok.insert(*m, ok);
    }
    // Conditions shared by several stages, used only as their conditions, are inlined too.
    let member = |u: V| pass_ok.contains_key(&u) || taken.contains_key(&u);
    for &c in producers {
        if boolean(g, c)
            && !is_root.contains(&c)
            && !bans.contains(&Ban::Inline(c))
            && !mul_guards.contains(&c)
            && cx.users(c).iter().all(|&u| member(u) && arms_of(g, u).iter().all(|&(_, x)| x != c))
            && !cx.users(c).is_empty()
        {
            inline_cond.insert(c);
        }
    }
    // The final deciders, with every inlined condition.
    let mut plan = Plan { absorbed: taken.keys().copied().collect(), inline_cond, ..Default::default() };
    for (m, a, _) in &roots {
        let inl = |c: V| plan.inline_cond.contains(&c);
        let arms = cx.flatten(*m, a, &inl)?;
        let mut deciders: Vec<(SDnf, Out)> = Vec::new();
        for (d, out) in outputs(g, arms, &pass_ok[m], &inl)? {
            match deciders.iter_mut().find(|(_, o)| *o == out && !matches!(o, Out::Mul(..))) {
                Some((dd, _)) => {
                    for t in d {
                        if !dd.contains(&t) {
                            dd.push(t);
                        }
                    }
                }
                None => deciders.push((d, out)),
            }
        }
        if !a.is_empty() && deciders.iter().any(|(d, _)| d.iter().map(|t| t.len()).sum::<usize>() > MAX_LITS) {
            return Err(Ban::Absorb(*a.last().unwrap()));
        }
        let mut passes: Vec<V> = Vec::new();
        for (_, o) in &deciders {
            if let Out::Pass(x) = *o {
                if !passes.contains(&x) {
                    passes.push(x);
                }
            }
        }
        // Wires: the pass on the cluster's wire is the one leaving the fewest values to move
        // to the bus; the deciders of the others may read no other pass.
        if passes.len() > 1 {
            let mut best: Option<(usize, usize)> = None;
            for (i, &p) in passes.iter().enumerate() {
                let mut forced = 0;
                let mut ok = true;
                for (d, o) in &deciders {
                    let r = Stage::reads(d, o);
                    let ps: Vec<V> = r.iter().copied().filter(|v| passes.contains(v)).collect();
                    if ps.iter().any(|&q| q != p) {
                        ok &= ps.len() == 1;
                        forced += r.len() - 1;
                    }
                }
                if ok && best.is_none_or(|(_, f)| forced < f) {
                    best = Some((i, forced));
                }
            }
            let Some((i, _)) = best else {
                // Give up the pass most read by the other deciders (it would be on the bus
                // anyway, as their condition).
                let read_by_others = |q: V| deciders.iter().filter(|(d, o)| *o != Out::Pass(q) && Stage::reads(d, o).contains(&q)).count();
                let q = passes.iter().copied().rev().max_by_key(|&q| read_by_others(q)).unwrap();
                return Err(Ban::Pass(q));
            };
            let p = passes.remove(i);
            passes.insert(0, p);
            for (d, o) in &deciders {
                let r = Stage::reads(d, o);
                if r.iter().any(|v| passes[1..].contains(v)) {
                    plan.force_bus.extend(r.into_iter().filter(|v| !passes.contains(v)));
                }
            }
        }
        plan.stages.insert(*m, Stage { deciders, passes });
    }
    // A passed select writes the outer select's signal, so it can't pass values under its own.
    for st in plan.stages.values() {
        if let Some(&x) = st.passes.iter().find(|&&x| plan.has_pass(x)) {
            return Err(Ban::Pass(x));
        }
    }
    Ok(plan)
}
