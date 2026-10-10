//! Expression lowering: Ticky (Python) semantics expressed as Factorio-native IR operations.

use ticky_factorio::{ArOp, CmpOp};
use ticky_syntax::ast::{self, BinOp, BoolOp, Expr, ExprKind, UnOp};
use ticky_syntax::{Diag, Span};

use crate::bundle::{self, Kind};
use crate::ir::{BTerm, Graph, V};

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
            if bundle::kind(g, x) == Kind::Bundle {
                let m = g.konst(-1);
                return Ok(g.bun(vec![BTerm::Map(ArOp::Mul, x, m)]));
            }
            let x = bundle::int(g, x, inner.span)?;
            let z = g.konst(0);
            g.ar(ArOp::Sub, z, x)
        }
        ExprKind::Unary(UnOp::Pos, inner) => expr(g, names, inner)?,
        ExprKind::Unary(UnOp::Invert, inner) => {
            let x = expr(g, names, inner)?;
            let m = g.konst(-1);
            if bundle::kind(g, x) == Kind::Bundle {
                return Ok(g.bun(vec![BTerm::Map(ArOp::Xor, x, m)]));
            }
            let x = bundle::int(g, x, inner.span)?;
            g.ar(ArOp::Xor, x, m)
        }
        ExprKind::Binary(op, a, b) => {
            if *op == BinOp::Div {
                return Err(Diag::error(e.span, "`/` makes a float, and Ticky has no floats")
                    .with_help("use `//` for integer division (or `tdiv(a, b)` for Factorio's truncating division)"));
            }
            let (x, y) = (expr(g, names, a)?, expr(g, names, b)?);
            if bundle::kind(g, x).is_signal() || bundle::kind(g, y).is_signal() {
                return Err(Diag::error(e.span, "signals can't be used in arithmetic")
                    .with_help("a signal names a bundle entry: read its value with `b[s]`"));
            }
            if bundle::kind(g, x) == Kind::Bundle || bundle::kind(g, y) == Kind::Bundle {
                return bundle::binop(g, *op, x, y, e.span);
            }
            let (x, y) = (bundle::int(g, x, a.span)?, bundle::int(g, y, b.span)?);
            // Inside a bundle comprehension, `//` and `%` truncate like Factorio (SPEC §4.3.5).
            if g.in_comp > 0 || g.uses_each(x) || g.uses_each(y) {
                match op {
                    BinOp::FloorDiv => return Ok(g.ar(ArOp::Div, x, y)),
                    BinOp::Mod => return Ok(g.ar(ArOp::Mod, x, y)),
                    _ => {}
                }
            }
            if matches!(op, BinOp::FloorDiv | BinOp::Mod) {
                div_check(g, y, e.span);
            }
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
            let (x, y) = (bundle::int(g, x, a.span)?, bundle::int(g, y, b.span)?);
            div_check(g, y, first.span);
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
            let mut left_span = first.span;
            let mut acc: Option<V> = None;
            for (op, right) in rest {
                let r = expr(g, names, right)?;
                let (kl, kr) = (bundle::kind(g, left), bundle::kind(g, r));
                let special = match op {
                    ast::CmpOp::In | ast::CmpOp::NotIn => {
                        let key = match kl {
                            Kind::Signal => bundle::Key::Const(g.as_sig(left).unwrap()),
                            Kind::SigVal => bundle::Key::Dyn(g.unsig(left)),
                            _ => return Err(Diag::error(left_span, "expected a signal here").with_help("write S(\"name\"), a signal constant or a `Signal` value")),
                        };
                        let b = bundle::bundle(g, r, right.span)?;
                        let x = bundle::get(g, b, key);
                        let z = g.konst(0);
                        Some(g.cmp(if *op == ast::CmpOp::In { CmpOp::Ne } else { CmpOp::Eq }, x, z))
                    }
                    ast::CmpOp::Eq | ast::CmpOp::Ne if kl == Kind::Bundle && kr == Kind::Bundle => {
                        Some(bundle::equal(g, left, r, *op == ast::CmpOp::Eq))
                    }
                    ast::CmpOp::Eq | ast::CmpOp::Ne if kl == Kind::Signal && kr == Kind::Signal => {
                        let same = g.as_sig(left) == g.as_sig(r);
                        Some(g.konst((same == (*op == ast::CmpOp::Eq)) as i32))
                    }
                    // A runtime signal: compare the one-hot bundles.
                    ast::CmpOp::Eq | ast::CmpOp::Ne if kl.is_signal() && kr.is_signal() => {
                        let (a, b) = (g.unsig(left), g.unsig(r));
                        Some(bundle::equal(g, a, b, *op == ast::CmpOp::Eq))
                    }
                    _ => None,
                };
                let c = match special {
                    Some(c) => c,
                    None => {
                        if kl.is_signal() || kr.is_signal() {
                            return Err(Diag::error(e.span, "signals can only be compared with `==` and `!=` (with other signals)"));
                        }
                        if kl == Kind::Bundle || kr == Kind::Bundle {
                            return Err(Diag::error(e.span, "bundles can only be compared with `==` and `!=`")
                                .with_help("to compare each signal, use a comprehension, e.g. `{s: v for s, v in b.items() if v > 10}`"));
                        }
                        let (l, rr) = (bundle::int(g, left, left_span)?, bundle::int(g, r, right.span)?);
                        let op = match op {
                            ast::CmpOp::Lt => CmpOp::Lt,
                            ast::CmpOp::Gt => CmpOp::Gt,
                            ast::CmpOp::Eq => CmpOp::Eq,
                            ast::CmpOp::Ge => CmpOp::Ge,
                            ast::CmpOp::Le => CmpOp::Le,
                            ast::CmpOp::Ne => CmpOp::Ne,
                            _ => return Err(Diag::error(e.span, "`is` isn't supported").with_help("compare with `==` instead")),
                        };
                        g.cmp(op, l, rr)
                    }
                };
                acc = Some(match acc {
                    None => c,
                    Some(prev) => g.ar(ArOp::And, prev, c),
                });
                left = r;
                left_span = right.span;
            }
            acc.unwrap()
        }
        ExprKind::BoolOp(op, items) => {
            let mut acc = expr(g, names, &items[0])?;
            for item in &items[1..] {
                // The right side only runs when the left doesn't decide the result.
                let t = g.truth(acc);
                let runs = if *op == BoolOp::And { t } else { g.not(t) };
                g.path.push(runs);
                let next = expr(g, names, item);
                g.path.pop();
                let next = next?;
                same_kind(g, acc, next, item.span)?;
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
            let t = g.truth(c);
            g.path.push(t);
            let a = expr(g, names, then);
            g.path.pop();
            let nt = g.not(t);
            g.path.push(nt);
            let b = expr(g, names, orelse);
            g.path.pop();
            let (a, b) = (a?, b?);
            same_kind(g, a, b, orelse.span)?;
            g.mux(c, a, b)
        }
        ExprKind::Call { func, args, kwargs } => {
            if let ExprKind::Attr(base, m) = &func.kind {
                return method(g, names, base, m, args, kwargs, e.span);
            }
            let ExprKind::Name(fname) = &func.kind else {
                return Err(Diag::error(func.span, "only named functions can be called"));
            };
            match fname.as_str() {
                f if f.starts_with('#') && f.contains('.') => return crate::stdlib::lower_call(g, names, f, args, kwargs, e.span),
                "#drawb" => return crate::display::lower_draw(g, names, args, e.span),
                "S" => return Ok(g.sigk(bundle::s_call(args, kwargs, e.span)?)),
                // Internal: `b[k] = x` (from the expansion pass).
                "#bset" => {
                    let b = expr(g, names, &args[0])?;
                    let b = bundle::bundle(g, b, args[0].span).map_err(|_| Diag::error(args[0].span, "only bundles and arrays can be indexed"))?;
                    let k = bundle::key_any(g, names, &args[1])?;
                    let x = expr(g, names, &args[2])?;
                    let x = bundle::int(g, x, args[2].span)?;
                    return Ok(bundle::set(g, b, k, x));
                }
                // Internal (bundle iteration, `nth`): `#rank(b, k, max)` is the signal of `b`
                // ranked `k` (from the largest if `max`) with its value, as a bundle;
                // `#hot(x)` that bundle's signal; `#total(x)` its value.
                "#rank" => {
                    let b = expr(g, names, &args[0])?;
                    let b = bundle::bundle(g, b, args[0].span)?;
                    let k = expr(g, names, &args[1])?;
                    let k = bundle::int(g, k, args[1].span)?;
                    let max = matches!(args[2].kind, ExprKind::Bool(true));
                    return Ok(g.brank_at(b, max, k));
                }
                "#hot" => {
                    let b = expr(g, names, &args[0])?;
                    return Ok(g.onehot(b));
                }
                "#total" => {
                    let b = expr(g, names, &args[0])?;
                    return Ok(g.btotal(b));
                }
                "Bundle" => return bundle::construct(g, names, args, kwargs, e.span),
                // Internal: signal arrays (from the expansion pass). A bank of an array is a
                // bundle with element `k` on `Graph::slot(k)`; the last argument (a literal) is
                // the bank's length.
                "#arr" => {
                    // Elements with the same value share a term: a table of ones on their
                    // slots times the value (`[x] * n` is one combinator, not n).
                    let mut groups: Vec<(V, Vec<usize>)> = Vec::new();
                    let mut konst = Vec::new();
                    for (k, a) in args.iter().enumerate() {
                        let x = expr(g, names, a)?;
                        let x = bundle::int(g, x, a.span)?;
                        match g.as_const(x) {
                            Some(c) => konst.push((Graph::slot(k), c)),
                            None => match groups.iter_mut().find(|(v, _)| *v == x) {
                                Some((_, ks)) => ks.push(k),
                                None => groups.push((x, vec![k])),
                            },
                        }
                    }
                    let mut terms = vec![BTerm::K(crate::ir::normalize(konst))];
                    for (x, ks) in groups {
                        if let [k] = ks[..] {
                            terms.push(BTerm::One(Graph::slot(k), x));
                        } else {
                            let ones = g.bconst(ks.iter().map(|&k| (Graph::slot(k), 1)));
                            terms.push(BTerm::Map(ArOp::Mul, ones, x));
                        }
                    }
                    return Ok(g.bun(terms));
                }
                "#aget" | "#aset" | "#aadd" | "#azeros" | "#asorted" | "#amax" | "#amin" | "#aidx" => {
                    let n = match args.last().map(|a| &a.kind) {
                        Some(ExprKind::Int(n)) => *n as usize,
                        _ => unreachable!("array builtins end with the length"),
                    };
                    let mut vals = Vec::new();
                    for a in &args[..args.len() - 1] {
                        vals.push(expr(g, names, a)?);
                    }
                    let b = vals.first().copied().unwrap_or(0);
                    return Ok(match fname.as_str() {
                        "#aget" => g.aget(b, vals[1], n),
                        "#aset" => g.aset(b, vals[1], vals[2], n),
                        "#aadd" => g.aadd(b, vals[1], vals[2], n),
                        "#azeros" => g.azeros(b, vals[1], n),
                        "#asorted" => {
                            let rev = g.as_const(vals[1]).unwrap_or(0) != 0;
                            g.asorted(b, n, rev)
                        }
                        "#amax" => g.amax(b, n, true),
                        "#amin" => g.amax(b, n, false),
                        _ => g.positions(n),
                    });
                }
                "len" if args.len() == 1 => {
                    let b = expr(g, names, &args[0])?;
                    let b = bundle::bundle(g, b, args[0].span)?;
                    return Ok(g.bcount(b));
                }
                "sum" | "max" | "min" if args.len() == 1 => {
                    let ExprKind::Call { func: vf, args: va, .. } = &args[0].kind else {
                        return Err(Diag::error(e.span, format!("`{fname}` of a single value")).with_help(format!("for a bundle, write `{fname}(b.values())`")));
                    };
                    let ExprKind::Attr(base, m) = &vf.kind else {
                        return Err(Diag::error(e.span, format!("`{fname}` of a single value")));
                    };
                    if m != "values" || !va.is_empty() {
                        return Err(Diag::error(args[0].span, format!("`{fname}` of a bundle needs `.values()`")));
                    }
                    let b = expr(g, names, base)?;
                    let b = bundle::bundle(g, b, base.span)?;
                    return Ok(match fname.as_str() {
                        "sum" => g.btotal(b),
                        f => {
                            let one = g.bselect(b, f == "max");
                            g.btotal(one)
                        }
                    });
                }
                _ => {}
            }
            if let Some((k, _)) = kwargs.first() {
                return Err(Diag::error(e.span, format!("`{fname}` doesn't take a keyword argument `{k}`")));
            }
            let mut vals: Vec<V> = Vec::new();
            for a in args {
                let v = expr(g, names, a)?;
                vals.push(bundle::int(g, v, a.span)?);
            }
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
                // Internal (`--checks`): `#chk(i, n, x)` is `x`, an element at runtime index `i`
                // of an array of `n`, checking the index.
                "#chk" => {
                    let n = vals[1];
                    let z = g.konst(0);
                    let (lo, hi) = (g.cmp(CmpOp::Lt, vals[0], z), g.cmp(CmpOp::Ge, vals[0], n));
                    let bad = g.ar(ArOp::Or, lo, hi);
                    g.check(bad, e.span, "index out of range");
                    vals[2]
                }
                // Internal (`--checks`): `#ixok(i, n)`: is `i` a valid index for an array of `n`.
                "#ixok" => {
                    let n = vals[1];
                    let z = g.konst(0);
                    let (lo, hi) = (g.cmp(CmpOp::Ge, vals[0], z), g.cmp(CmpOp::Lt, vals[0], n));
                    g.ar(ArOp::And, lo, hi)
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
                "print" | "len" | "sum" | "sorted" | "range" | "port" => {
                    return Err(Diag::error(e.span, format!("`{fname}` isn't available here yet")))
                }
                _ => {
                    return Err(Diag::error(func.span, format!("unknown function `{fname}`"))
                        .with_help("user-defined functions (`def`) arrive in a later level"))
                }
            }
        }
        ExprKind::Attr(base, name) => {
            let b = expr(g, names, base)?;
            let b = bundle::bundle(g, b, base.span)?;
            let sig = bundle::ident(name, e.span);
            g.bget(b, sig)
        }
        ExprKind::Index(base, idx) => {
            let b = expr(g, names, base)?;
            let b = bundle::bundle(g, b, base.span).map_err(|_| Diag::error(base.span, "only bundles and arrays can be indexed"))?;
            let k = bundle::key_any(g, names, idx)?;
            bundle::get(g, b, k)
        }
        ExprKind::Dict(items) => bundle::dict(g, names, items)?,
        ExprKind::DictComp { key, value, target, iter, conds } => {
            g.in_comp += 1;
            let r = bundle::comprehension(g, names, key, value, target, iter, conds, e.span);
            g.in_comp -= 1;
            r?
        }
        ExprKind::Tuple(_) | ExprKind::List(_) | ExprKind::ListComp { .. } => {
            return Err(Diag::error(e.span, "tuples and lists can only be used in assignments like `a, b = b, a`"))
        }
    })
}

/// With `--checks`: division (or remainder) by `y` fails when `y` is 0.
pub fn div_check(g: &mut Graph, y: V, span: Span) {
    let z = g.konst(0);
    let zero = g.cmp(CmpOp::Eq, y, z);
    g.check(zero, span, "division by zero");
}

/// Both sides of a select (or `and`/`or`) must be the same kind of value.
fn same_kind(g: &Graph, a: V, b: V, span: Span) -> Result<(), Diag> {
    let (ka, kb) = (bundle::kind(g, a), bundle::kind(g, b));
    if ka != kb && !(ka.is_signal() && kb.is_signal()) {
        let name = |k: Kind| match k {
            Kind::Int => "a number",
            Kind::Bundle => "a bundle",
            Kind::Signal | Kind::SigVal => "a signal",
        };
        return Err(Diag::error(span, format!("this is {}, but the other side is {}", name(kb), name(ka))));
    }
    Ok(())
}

/// `b.method(...)` on a bundle.
fn method(g: &mut Graph, names: &mut dyn Names, base: &Expr, m: &str, args: &[Expr], kwargs: &[(String, Expr)], span: Span) -> Result<V, Diag> {
    let b = expr(g, names, base)?;
    // `s.value_in(b)` is `b[s]`.
    if bundle::kind(g, b).is_signal() {
        let [arg] = args else {
            return Err(Diag::error(span, format!("signals have no method `{m}` with {} argument(s)", args.len())).with_help("signals have `.value_in(bundle)`"));
        };
        if m != "value_in" {
            return Err(Diag::error(span, format!("signals have no method `{m}`")).with_help("signals have `.value_in(bundle)`"));
        }
        let key = if let Some(s) = g.as_sig(b) { bundle::Key::Const(s) } else { bundle::Key::Dyn(g.unsig(b)) };
        let x = expr(g, names, arg)?;
        let x = bundle::bundle(g, x, arg.span)?;
        return Ok(bundle::get(g, x, key));
    }
    let b = bundle::bundle(g, b, base.span).map_err(|_| Diag::error(base.span, format!("`.{m}()` needs a bundle")))?;
    if let Some((k, _)) = kwargs.first() {
        return Err(Diag::error(span, format!("`.{m}()` doesn't take a keyword argument `{k}`")));
    }
    match (m, args) {
        ("total", []) => Ok(g.btotal(b)),
        // The signal with the largest (smallest) value; ties in the game's signal order
        // (`SignalTable::rank`); no signal for an empty bundle.
        ("argmax", []) => {
            let top = g.brank(b, true, 0);
            Ok(g.onehot(top))
        }
        ("argmin", []) => {
            let top = g.brank(b, false, 0);
            Ok(g.onehot(top))
        }
        ("nth", _) => Err(Diag::error(span, "`.nth(k)` gives a signal and its value: unpack it, e.g. `s, v = b.nth(0)`")),
        ("get", [k]) | ("get", [k, _]) => {
            let key = bundle::key_any(g, names, k)?;
            let x = bundle::get(g, b, key);
            if let [_, d] = args {
                // Like dict.get: the default when the signal is missing (0).
                let dv = expr(g, names, d)?;
                let dv = bundle::int(g, dv, d.span)?;
                let z = g.konst(0);
                let has = g.cmp(CmpOp::Ne, x, z);
                return Ok(g.mux(has, x, dv));
            }
            Ok(x)
        }
        ("values" | "items" | "keys", _) => Err(Diag::error(span, format!("`.{m}()` can only be used inside `sum`, `min`, `max` or a comprehension"))),
        _ => Err(Diag::error(span, format!("bundles have no method `{m}` with {} argument(s)", args.len()))
            .with_help("bundle methods: `.total()`, `.get(sig, default)`, `.argmax()`, `.argmin()`, `.nth(k)`, `.items()` (in comprehensions and `for` loops), `.values()` (in sum/min/max)")),
    }
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
