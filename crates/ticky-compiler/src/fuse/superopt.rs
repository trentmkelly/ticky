//! Superoptimisation (PLAN.md §4): harvesting small scalar patterns with what codegen spends
//! on them (`TICKY_SUPEROPT_HARVEST=file`, read by `tools/superopt`).

use std::collections::{HashMap, HashSet};
use std::io::Write;

use ticky_factorio::{ArOp, CmpOp, EntId, Netlist};

use crate::ir::{Graph, Op, V};

/// Most operations and leaves in a harvested pattern.
const MAX_OPS: usize = 4;
const MAX_LEAVES: usize = 3;

pub fn harvesting() -> bool {
    std::env::var_os("TICKY_SUPEROPT_HARVEST").is_some()
}

pub fn ar_name(op: ArOp) -> &'static str {
    match op {
        ArOp::Mul => "mul",
        ArOp::Div => "div",
        ArOp::Add => "add",
        ArOp::Sub => "sub",
        ArOp::Mod => "mod",
        ArOp::Pow => "pow",
        ArOp::Shl => "shl",
        ArOp::Shr => "shr",
        ArOp::And => "and",
        ArOp::Or => "or",
        ArOp::Xor => "xor",
    }
}

pub fn cmp_name(op: CmpOp) -> &'static str {
    match op {
        CmpOp::Lt => "lt",
        CmpOp::Gt => "gt",
        CmpOp::Eq => "eq",
        CmpOp::Ge => "ge",
        CmpOp::Le => "le",
        CmpOp::Ne => "ne",
    }
}

fn is_scalar_op(g: &Graph, v: V) -> bool {
    matches!(g.op(v), Op::Ar(..) | Op::Cmp(..) | Op::Mux { .. } | Op::Dec(_) | Op::Sel(_))
}

/// Appends one line per pattern of one `logic()` call to the harvest file: the combinators
/// emitted for its nodes, its shape (an s-expression over leaves `x0…` and constants), the
/// kinds of its leaves (`s` source, `v` a value computed elsewhere, `r` a bundle read, `o` other,
/// each with its interval: `s:lo:hi`, comma-separated)
/// and where its result goes (`root`, or the consumer's kind). Patterns are the maximal trees
/// of scalar operations used only inside the tree, with at most [`MAX_OPS`] operations and
/// [`MAX_LEAVES`] distinct leaves; bigger trees are split at their maximal such subtrees.
/// `marks`: the emission loop's (node, first entity) marks, `net` the entities.
pub fn harvest(g: &Graph, live: &[V], roots: &[V], marks: &[(V, EntId)], net: &Netlist, what: &str) {
    let Some(path) = std::env::var_os("TICKY_SUPEROPT_HARVEST") else { return };
    let mut cost: HashMap<V, usize> = HashMap::new();
    for (i, &(v, from)) in marks.iter().enumerate() {
        let to = marks.get(i + 1).map_or(net.entities.len(), |m| m.1).min(net.entities.len());
        let n = net.entities[from.min(to)..to].iter().filter(|e| e.kind.is_combinator()).count();
        *cost.entry(v).or_default() += n;
    }
    let mut users: HashMap<V, Vec<V>> = HashMap::new();
    for &v in live {
        for o in g.operands(v) {
            let u = users.entry(o).or_default();
            if !u.contains(&v) {
                u.push(v);
            }
        }
    }
    let root_set: HashSet<V> = roots.iter().copied().collect();
    // Inner: a scalar op used by exactly one node and not a root.
    let inner = |v: V| is_scalar_op(g, v) && !root_set.contains(&v) && users.get(&v).is_some_and(|u| u.len() == 1);
    // Size of the tree under `v` (ops, leaves), unbounded.
    fn size(g: &Graph, v: V, inner: &dyn Fn(V) -> bool, ops: &mut usize, leaves: &mut Vec<V>) {
        *ops += 1;
        for o in g.operands(v) {
            if g.as_const(o).is_some() {
                continue;
            }
            if inner(o) {
                size(g, o, inner, ops, leaves);
            } else if !leaves.contains(&o) {
                leaves.push(o);
            }
        }
    }
    let fits = |v: V| {
        let (mut ops, mut leaves) = (0, Vec::new());
        size(g, v, &inner, &mut ops, &mut leaves);
        ops <= MAX_OPS && leaves.len() <= MAX_LEAVES
    };
    // A header per call: size builds compile several candidates, which the tool tells apart.
    let mut out = format!("#\t{what}\n");
    for &v in live {
        if !is_scalar_op(g, v) || !fits(v) {
            continue;
        }
        // Maximal: the parent (if this is inner) doesn't fit.
        if inner(v) && fits(users[&v][0]) {
            continue;
        }
        let mut leaves: Vec<V> = Vec::new();
        let mut total = 0;
        let shape = show(g, v, &inner, &mut leaves, &cost, &mut total);
        let kinds: Vec<String> = leaves
            .iter()
            .map(|&l| {
                let k = match g.op(l) {
                    Op::Src(_) => 's',
                    Op::BGet(..) | Op::BTotal(_) | Op::BCount(_) | Op::AGet(..) | Op::BDot(..) => 'r',
                    _ if is_scalar_op(g, l) => 'v',
                    _ => 'o',
                };
                let iv = g.iv(l);
                format!("{k}:{}:{}", iv.lo, iv.hi)
            })
            .collect();
        let kinds = if kinds.is_empty() { "-".to_string() } else { kinds.join(",") };
        let to = if root_set.contains(&v) {
            "root".to_string()
        } else {
            match users.get(&v).map(|u| u.as_slice()) {
                Some([u]) => kind_name(g.op(*u)).to_string(),
                Some(u) => format!("shared{}", u.len()),
                None => "none".to_string(),
            }
        };
        out.push_str(&format!("{total}\t{shape}\t{kinds}\t{to}\t{what}\n"));
    }
    if let Ok(mut f) = std::fs::OpenOptions::new().create(true).append(true).open(path) {
        let _ = f.write_all(out.as_bytes());
    }
}

fn kind_name(op: &Op) -> &'static str {
    match op {
        Op::Ar(..) => "ar",
        Op::Cmp(..) => "cmp",
        Op::Mux { .. } => "mux",
        Op::Dec(_) => "dec",
        Op::Sel(_) => "sel",
        Op::Bun(_) => "bun",
        Op::BDec(_) | Op::BMux { .. } => "bsel",
        _ => "other",
    }
}

fn show(g: &Graph, v: V, inner: &dyn Fn(V) -> bool, leaves: &mut Vec<V>, cost: &HashMap<V, usize>, total: &mut usize) -> String {
    *total += cost.get(&v).copied().unwrap_or(0);
    let mut sub = |o: V| -> String {
        if let Some(k) = g.as_const(o) {
            k.to_string()
        } else if inner(o) {
            show(g, o, inner, leaves, cost, total)
        } else {
            let i = leaves.iter().position(|&l| l == o).unwrap_or_else(|| {
                leaves.push(o);
                leaves.len() - 1
            });
            format!("x{i}")
        }
    };
    match g.op(v).clone() {
        Op::Ar(op, a, b) => format!("({} {} {})", ar_name(op), sub(a), sub(b)),
        Op::Cmp(op, a, b) => format!("({} {} {})", cmp_name(op), sub(a), sub(b)),
        // An arm worth 0 doesn't read its condition (`Graph::operands`).
        Op::Mux { t, f, a, b } => {
            let zero = |x: V| g.as_const(x) == Some(0);
            let t = if zero(a) { "_".to_string() } else { sub(t) };
            let f = if zero(b) { "_".to_string() } else { sub(f) };
            format!("(mux {t} {f} {} {})", sub(a), sub(b))
        }
        Op::Dec(arms) => {
            let mut s = String::from("(dec");
            for (d, k) in arms {
                s.push_str(&format!(" (arm {k} (or"));
                for t in d {
                    s.push_str(" (and");
                    for l in t {
                        s.push_str(&format!(" ({} {} {})", cmp_name(l.op), sub(l.a), sub(l.b)));
                    }
                    s.push(')');
                }
                s.push_str("))");
            }
            s.push(')');
            s
        }
        Op::Sel(arms) => {
            let mut s = String::from("(sel");
            for (c, x) in arms.into_iter().filter(|(_, x)| g.as_const(*x) != Some(0)) {
                s.push_str(&format!(" {} {}", sub(c), sub(x)));
            }
            s.push(')');
            s
        }
        _ => unreachable!("not a scalar op"),
    }
}

thread_local! {
    static NO_PICKS: std::cell::Cell<bool> = const { std::cell::Cell::new(false) };
}

/// Whether codegen may pick select arms off the bus with one decider (`codegen/selects.rs`,
/// `Out::Pick`): the superoptimiser's main find. Off with `TICKY_NO_PICK=1` or
/// [`set_picks_disabled`].
pub fn picks_enabled() -> bool {
    !NO_PICKS.with(|c| c.get()) && std::env::var_os("TICKY_NO_PICK").is_none()
}

/// Turns picks off (or back on) for compilations on this thread (tests compare both).
pub fn set_picks_disabled(off: bool) {
    NO_PICKS.with(|c| c.set(off));
}
