//! Expression lowering: Ticky (Python) semantics expressed as Factorio-native IR operations.

use ticky_factorio::{ArOp, CmpOp};
use ticky_syntax::ast::{self, BinOp, BoolOp, Expr, ExprKind, UnOp};
use ticky_syntax::{Diag, Span};

use crate::ir::{Graph, V};

/// Resolves names to values; implemented differently for constants, blocks and tests.
pub trait Names {
    fn lookup(&mut self, g: &mut Graph, name: &str, span: Span) -> Result<V, Diag>;

    /// `ticks()`: ticks since the program started.
    fn ticks(&mut self, _g: &mut Graph, span: Span) -> Result<V, Diag> {
        Err(Diag::error(span, "`ticks()` can't be used here"))
    }
}

pub fn expr(g: &mut Graph, names: &mut dyn Names, e: &Expr) -> Result<V, Diag> {
    Ok(match &e.kind {
        ExprKind::Int(v) => {
            if *v > i32::MAX as i64 {
                return Err(Diag::error(e.span, "integer literal is larger than 2147483647")
                    .with_help("Ticky integers are 32-bit, like Factorio signals"));
            }
            g.konst(*v as i32)
        }
        ExprKind::Bool(b) => g.konst(*b as i32),
        ExprKind::Name(n) => names.lookup(g, n, e.span)?,
        ExprKind::Str(_) => {
            return Err(Diag::error(e.span, "strings can't be used as values")
                .with_help("Ticky has no string type; strings are only used for signal names and labels"))
        }
        ExprKind::Unary(UnOp::Neg, inner) => {
            // -2147483648 is a valid literal even though 2147483648 is not.
            if let ExprKind::Int(v) = inner.kind {
                if v == 1 << 31 {
                    return Ok(g.konst(i32::MIN));
                }
            }
            let x = expr(g, names, inner)?;
            let z = g.konst(0);
            g.ar(ArOp::Sub, z, x)
        }
        ExprKind::Unary(UnOp::Pos, inner) => expr(g, names, inner)?,
        ExprKind::Unary(UnOp::Invert, inner) => {
            let x = expr(g, names, inner)?;
            let m = g.konst(-1);
            g.ar(ArOp::Xor, x, m)
        }
        ExprKind::Binary(op, a, b) => {
            if *op == BinOp::Div {
                return Err(Diag::error(e.span, "`/` makes a float, and Ticky has no floats")
                    .with_help("use `//` for integer division (or `tdiv(a, b)` for Factorio's truncating division)"));
            }
            let (x, y) = (expr(g, names, a)?, expr(g, names, b)?);
            binop(g, *op, x, y)
        }
        // `a % b == 0` doesn't depend on the remainder's sign, so skip Python's correction.
        ExprKind::Compare(first, rest)
            if rest.len() == 1
                && matches!(rest[0].0, ast::CmpOp::Eq | ast::CmpOp::Ne)
                && matches!(rest[0].1.kind, ExprKind::Int(0))
                && matches!(first.kind, ExprKind::Binary(BinOp::Mod, ..)) =>
        {
            let ExprKind::Binary(_, a, b) = &first.kind else { unreachable!() };
            let (x, y) = (expr(g, names, a)?, expr(g, names, b)?);
            let r = match log2_const(g, y) {
                Some(k) => {
                    let mask = g.konst((1 << k) - 1);
                    g.ar(ArOp::And, x, mask)
                }
                None => g.ar(ArOp::Mod, x, y),
            };
            let z = g.konst(0);
            g.cmp(if rest[0].0 == ast::CmpOp::Eq { CmpOp::Eq } else { CmpOp::Ne }, r, z)
        }
        ExprKind::Compare(first, rest) => {
            let mut left = expr(g, names, first)?;
            let mut acc: Option<V> = None;
            for (op, right) in rest {
                let r = expr(g, names, right)?;
                let op = match op {
                    ast::CmpOp::Lt => CmpOp::Lt,
                    ast::CmpOp::Gt => CmpOp::Gt,
                    ast::CmpOp::Eq => CmpOp::Eq,
                    ast::CmpOp::Ge => CmpOp::Ge,
                    ast::CmpOp::Le => CmpOp::Le,
                    ast::CmpOp::Ne => CmpOp::Ne,
                    _ => {
                        return Err(Diag::error(e.span, "`in` and `is` aren't supported yet")
                            .with_help("compare with `==` instead"))
                    }
                };
                let c = g.cmp(op, left, r);
                acc = Some(match acc {
                    None => c,
                    Some(prev) => g.ar(ArOp::And, prev, c),
                });
                left = r;
            }
            acc.unwrap()
        }
        ExprKind::BoolOp(op, items) => {
            let mut acc = expr(g, names, &items[0])?;
            for item in &items[1..] {
                let next = expr(g, names, item)?;
                acc = if g.is_bool(acc) && g.is_bool(next) {
                    g.ar(if *op == BoolOp::And { ArOp::And } else { ArOp::Or }, acc, next)
                } else if *op == BoolOp::And {
                    // Python: `a and b` is `b` if a is truthy, else `a`.
                    g.mux(acc, next, acc)
                } else {
                    g.mux(acc, acc, next)
                };
            }
            acc
        }
        ExprKind::Not(inner) => {
            let x = expr(g, names, inner)?;
            let t = g.truth(x);
            g.not(t)
        }
        ExprKind::IfExp { cond, then, orelse } => {
            let c = expr(g, names, cond)?;
            let (a, b) = (expr(g, names, then)?, expr(g, names, orelse)?);
            g.mux(c, a, b)
        }
        ExprKind::Call { func, args, kwargs } => {
            let ExprKind::Name(fname) = &func.kind else {
                return Err(Diag::error(func.span, "methods aren't supported yet"));
            };
            if let Some((k, _)) = kwargs.first() {
                return Err(Diag::error(e.span, format!("`{fname}` doesn't take a keyword argument `{k}`")));
            }
            let vals: Vec<V> = args.iter().map(|a| expr(g, names, a)).collect::<Result<_, _>>()?;
            let arity = |n: usize| -> Result<(), Diag> {
                if vals.len() == n {
                    Ok(())
                } else {
                    Err(Diag::error(e.span, format!("`{fname}` takes {n} argument(s), got {}", vals.len())))
                }
            };
            match fname.as_str() {
                "abs" => {
                    arity(1)?;
                    let x = vals[0];
                    let z = g.konst(0);
                    let neg = g.cmp(CmpOp::Lt, x, z);
                    let nx = g.ar(ArOp::Sub, z, x);
                    g.mux(neg, nx, x)
                }
                "min" | "max" => {
                    if vals.len() < 2 {
                        return Err(Diag::error(e.span, format!("`{fname}` needs at least 2 arguments")));
                    }
                    let cmp = if fname == "min" { CmpOp::Lt } else { CmpOp::Gt };
                    let mut acc = vals[0];
                    for &v in &vals[1..] {
                        // Python keeps the first of equal values.
                        let better = g.cmp(cmp, v, acc);
                        acc = g.mux(better, v, acc);
                    }
                    acc
                }
                "clamp" => {
                    arity(3)?;
                    let (x, lo, hi) = (vals[0], vals[1], vals[2]);
                    let below = g.cmp(CmpOp::Lt, x, lo);
                    let x = g.mux(below, lo, x);
                    let above = g.cmp(CmpOp::Gt, x, hi);
                    g.mux(above, hi, x)
                }
                "tdiv" => {
                    arity(2)?;
                    g.ar(ArOp::Div, vals[0], vals[1])
                }
                "tmod" => {
                    arity(2)?;
                    g.ar(ArOp::Mod, vals[0], vals[1])
                }
                "int" => {
                    arity(1)?;
                    vals[0]
                }
                "bool" => {
                    arity(1)?;
                    g.truth(vals[0])
                }
                "ticks" => {
                    arity(0)?;
                    names.ticks(g, e.span)?
                }
                // Internal: `#select(i, x0, x1, …)` is `x_i`, or 0 when `i` is out of range.
                "#select" => {
                    let i = vals[0];
                    let mut arms = Vec::new();
                    for (k, &x) in vals[1..].iter().enumerate() {
                        let kv = g.konst(k as i32);
                        arms.push((g.cmp(CmpOp::Eq, i, kv), x));
                    }
                    g.sel(arms)
                }
                "print" | "len" | "sum" | "sorted" | "range" | "S" | "Bundle" | "port" => {
                    return Err(Diag::error(e.span, format!("`{fname}` isn't available here yet")))
                }
                _ => {
                    return Err(Diag::error(func.span, format!("unknown function `{fname}`"))
                        .with_help("user-defined functions (`def`) arrive in a later level"))
                }
            }
        }
        ExprKind::Attr(..) | ExprKind::Index(..) => {
            return Err(Diag::error(e.span, "bundles and arrays aren't supported yet"))
        }
        ExprKind::Tuple(_) | ExprKind::List(_) | ExprKind::ListComp { .. } => {
            return Err(Diag::error(e.span, "tuples and lists can only be used in assignments like `a, b = b, a`"))
        }
    })
}

pub fn binop(g: &mut Graph, op: BinOp, x: V, y: V) -> V {
    match op {
        BinOp::Add => g.ar(ArOp::Add, x, y),
        BinOp::Sub => g.ar(ArOp::Sub, x, y),
        BinOp::Mul => g.ar(ArOp::Mul, x, y),
        BinOp::Pow => g.ar(ArOp::Pow, x, y),
        BinOp::Shl => g.ar(ArOp::Shl, x, y),
        BinOp::Shr => g.ar(ArOp::Shr, x, y),
        BinOp::BitAnd => g.ar(ArOp::And, x, y),
        BinOp::BitOr => g.ar(ArOp::Or, x, y),
        BinOp::BitXor => g.ar(ArOp::Xor, x, y),
        BinOp::FloorDiv => floor_div(g, x, y),
        BinOp::Mod => floor_mod(g, x, y),
        BinOp::Div => unreachable!("rejected earlier"),
    }
}

/// 1 when Factorio's truncating division rounded toward zero but Python would round down,
/// i.e. when the remainder is non-zero and its sign differs from the divisor's.
fn floor_adjust(g: &mut Graph, r: V, b: V) -> V {
    let z = g.konst(0);
    let bi = g.iv(b);
    if bi.lo >= 1 {
        return g.cmp(CmpOp::Lt, r, z);
    }
    if bi.hi <= -1 {
        return g.cmp(CmpOp::Gt, r, z);
    }
    let nz = g.cmp(CmpOp::Ne, r, z);
    let rn = g.cmp(CmpOp::Lt, r, z);
    let bn = g.cmp(CmpOp::Lt, b, z);
    let differ = g.ar(ArOp::Xor, rn, bn);
    g.ar(ArOp::And, nz, differ)
}

/// `k` if `v` is the constant 2^k with k ≥ 1.
fn log2_const(g: &Graph, v: V) -> Option<i32> {
    g.as_const(v).filter(|&b| b > 1 && (b & (b - 1)) == 0).map(|b| b.trailing_zeros() as i32)
}

/// Python `//`: floors. Free when both operands are provably non-negative.
pub fn floor_div(g: &mut Graph, a: V, b: V) -> V {
    // Arithmetic shift right is floor division by a power of two, negatives included.
    if let Some(k) = log2_const(g, b) {
        let kv = g.konst(k);
        return g.ar(ArOp::Shr, a, kv);
    }
    let q = g.ar(ArOp::Div, a, b);
    if g.iv(a).nonneg() && g.iv(b).nonneg() {
        return q;
    }
    let r = g.ar(ArOp::Mod, a, b);
    let adj = floor_adjust(g, r, b);
    g.ar(ArOp::Sub, q, adj)
}

/// Python `%`: result takes the divisor's sign. Free when both operands are non-negative.
pub fn floor_mod(g: &mut Graph, a: V, b: V) -> V {
    // Masking is Python's modulo by a positive power of two, negatives included.
    if let Some(k) = log2_const(g, b) {
        let mask = g.konst((1 << k) - 1);
        return g.ar(ArOp::And, a, mask);
    }
    let r = g.ar(ArOp::Mod, a, b);
    if g.iv(a).nonneg() && g.iv(b).nonneg() {
        return r;
    }
    let adj = floor_adjust(g, r, b);
    let rb = g.ar(ArOp::Add, r, b);
    g.mux(adj, rb, r)
}

#[cfg(test)]
mod tests {
    use super::*;

    struct NoNames;
    impl Names for NoNames {
        fn lookup(&mut self, _: &mut Graph, n: &str, s: Span) -> Result<V, Diag> {
            Err(Diag::error(s, format!("unknown {n}")))
        }
    }

    fn eval(src: &str) -> i32 {
        let m = ticky_syntax::parse(&format!("x = {src}\n")).unwrap();
        let ast::StmtKind::Assign { value, .. } = &m.body[0].kind else { panic!() };
        let mut g = Graph::default();
        let v = expr(&mut g, &mut NoNames, value).unwrap();
        g.as_const(v).unwrap_or_else(|| panic!("{src} did not fold"))
    }

    #[test]
    fn python_semantics() {
        assert_eq!(eval("-7 // 2"), -4);
        assert_eq!(eval("7 // -2"), -4);
        assert_eq!(eval("-7 // -2"), 3);
        assert_eq!(eval("-7 % 2"), 1);
        assert_eq!(eval("7 % -2"), -1);
        assert_eq!(eval("-7 % -2"), -1);
        assert_eq!(eval("6 // 3"), 2);
        assert_eq!(eval("-6 % 3"), 0);
        assert_eq!(eval("5 // 0"), 0);
        assert_eq!(eval("5 % 0"), 0);
        assert_eq!(eval("2 ** 10"), 1024);
        assert_eq!(eval("-2 ** 2"), -4);
        assert_eq!(eval("~5"), -6);
        assert_eq!(eval("1 < 2 < 3"), 1);
        assert_eq!(eval("1 < 3 < 2"), 0);
        assert_eq!(eval("0 or 7"), 7);
        assert_eq!(eval("3 and 7"), 7);
        assert_eq!(eval("0 and 7"), 0);
        assert_eq!(eval("not 5"), 0);
        assert_eq!(eval("10 if 0 else 20"), 20);
        assert_eq!(eval("abs(-5) + min(3, 1, 2) + max(4, 9)"), 15);
        assert_eq!(eval("clamp(150, 0, 100)"), 100);
        assert_eq!(eval("tdiv(-7, 2)"), -3);
        assert_eq!(eval("-2147483648"), i32::MIN);
        assert_eq!(eval("2147483647 + 1"), i32::MIN);
        assert_eq!(eval("True + True"), 2);
        assert_eq!(eval("-7 // 4"), -2);
        assert_eq!(eval("-7 % 4"), 1);
        assert_eq!(eval("-8 % 4 == 0"), 1);
        assert_eq!(eval("-7 % 4 != 0"), 1);
    }
}
