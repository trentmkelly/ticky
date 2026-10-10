//! `import display`: screens made of lamps.
//!
//! `output s: display.Screen(W, H)` is rewritten, before expansion, into an ordinary module
//! variable: a signal array of `W × H` pixels, all 0 to begin with. The compiler keeps it
//! live and shows it on a `W × H` grid of lamps in packed-RGB mode: each lamp shows the low 24
//! bits of its pixel (`0xRRGGBB`), and a pixel of 0 is off. In code, `s[x, y]` is pixel
//! `s[y * W + x]` (row by row from the top left), `s.fill(c)` sets every pixel, and `s.width`
//! / `s.height` are constants.

use std::collections::{HashMap, HashSet};

use ticky_syntax::ast::{BinOp, BoolOp, CmpOp, Expr, ExprKind, Module, PortDir, Stmt, StmtKind};
use ticky_syntax::{Diag, Span};

use crate::ir::Cv;

/// A screen output: a grid of lamps showing a signal array.
#[derive(Clone, Debug)]
pub struct Screen {
    /// The declared name (`--display NAME=…`, messages).
    pub name: String,
    /// The signal array it shows: the name itself for a screen; a hidden array for a
    /// [`Digits`](ScreenKind::Digits) readout, whose name is an `int`.
    pub var: String,
    pub kind: ScreenKind,
    pub w: usize,
    pub h: usize,
    pub label: Option<String>,
    pub span: Span,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum ScreenKind {
    /// `display.Screen(W, H)`: pixels the program sets.
    Screen,
    /// `display.Digits(n)`: an `int` shown in `n` digits.
    Digits,
}

impl Screen {
    pub fn pixels(&self) -> usize {
        self.w * self.h
    }
}

/// Most pixels a screen may have.
pub const MAX_PIXELS: usize = 4096;

/// The program with its screens turned into arrays, and the screens.
pub fn desugar(m: &Module) -> Result<(Module, Vec<Screen>), Vec<Diag>> {
    let mut errs = Vec::new();
    let mut imported = HashSet::new();
    let mut consts: HashMap<String, Cv> = HashMap::new();
    let mut screens = Vec::new();
    // `display.Digits` readouts, with their colours.
    let mut readouts: Vec<(Screen, Expr)> = Vec::new();
    let mut body = Vec::new();
    for s in &m.body {
        match &s.kind {
            // Checked by `stdlib::imports`.
            StmtKind::Import(n) => {
                imported.insert(n.clone());
            }
            StmtKind::Port { dir, name, ty, signal, label } if display_type(ty).is_some() => {
                let what = display_type(ty).unwrap();
                if !imported.contains("display") {
                    errs.push(Diag::error(ty.span, format!("`display.{what}` needs `import display` first")));
                    continue;
                }
                let r = match what {
                    "Screen" => screen(*dir, name, ty, signal.is_some(), label.as_ref(), &consts, s.span),
                    _ => digits(*dir, name, ty, signal.is_some(), label.as_ref(), &consts, s.span).map(|(sc, colour)| {
                        readouts.push((sc.clone(), colour));
                        sc
                    }),
                };
                match r {
                    Ok(sc) => screens.push(sc),
                    Err(d) => errs.push(d),
                }
            }
            _ => {
                // Module constants, for screen sizes.
                if let StmtKind::Assign { targets, value } = &s.kind {
                    if let [Expr { kind: ExprKind::Name(n), .. }] = targets.as_slice() {
                        match crate::program::eval_const(value, &consts, &[]) {
                            Ok(v) => consts.insert(n.clone(), v),
                            Err(_) => consts.remove(n),
                        };
                    }
                }
                body.push(s.clone());
            }
        }
    }
    let mut names = HashSet::new();
    for sc in &screens {
        if !names.insert(sc.name.clone()) {
            errs.push(Diag::error(sc.span, format!("`{}` is declared twice", sc.name)));
        }
    }
    if !errs.is_empty() {
        return Err(errs);
    }
    if screens.is_empty() {
        return Ok((Module { body }, screens));
    }
    // A readout is an `int` variable, drawn on its hidden screen by a block (one for all
    // readouts) that runs as often as it can, without pipelining: small, and the delay
    // doesn't matter.
    let mut draw_all = Vec::new();
    for (sc, colour) in &readouts {
        let sp = sc.span;
        let n = (sc.w + 1) / 4;
        let target = ex(ExprKind::Name(sc.var.clone()), sp);
        let call = |m: &str, args: Vec<Expr>, kwargs: Vec<(String, Expr)>| Stmt {
            kind: StmtKind::Expr(ex(ExprKind::Call { func: Box::new(ex(ExprKind::Attr(Box::new(target.clone()), m.into()), sp)), args, kwargs }, sp)),
            span: sp,
        };
        draw_all.push(call("fill", vec![int(0, sp)], vec![]));
        draw_all.push(call("number", vec![int(0, sp), int(0, sp), ex(ExprKind::Name(sc.name.clone()), sp), colour.clone()], vec![("width".into(), int(n as i64, sp))]));
    }
    if let Some((sc, _)) = readouts.first() {
        body.push(Stmt { kind: StmtKind::Every { period: Some(ex(ExprKind::Name(NATURAL.into()), sc.span)), body: draw_all }, span: sc.span });
    }
    let by_name: HashMap<String, Screen> = screens.iter().filter(|s| s.kind == ScreenKind::Screen).map(|s| (s.name.clone(), s.clone())).collect();
    let mut by_var = by_name.clone();
    by_var.extend(readouts.iter().map(|(s, _)| (s.var.clone(), s.clone())));
    CONSTS.with(|c| *c.borrow_mut() = consts.clone());
    rewrite_body(&mut body, &by_var, &mut errs);
    if !errs.is_empty() {
        return Err(errs);
    }
    // Every pixel starts at 0 (a prologue value, so every process can read the screen).
    let mut out: Vec<Stmt> = screens
        .iter()
        .map(|sc| {
            let sp = sc.span;
            let zeros = bin(BinOp::Mul, ex(ExprKind::List(vec![int(0, sp)]), sp), int(sc.pixels() as i64, sp), sp);
            Stmt { kind: StmtKind::Assign { targets: vec![ex(ExprKind::Name(sc.var.clone()), sp)], value: zeros }, span: sp }
        })
        .collect();
    // A readout's number starts at 0.
    for (sc, _) in &readouts {
        let sp = sc.span;
        out.push(Stmt { kind: StmtKind::Assign { targets: vec![ex(ExprKind::Name(sc.name.clone()), sp)], value: int(0, sp) }, span: sp });
    }
    out.extend(body);
    Ok((Module { body: out }, screens))
}

/// The period of a block that runs as often as its depth allows, without pipelining (an
/// internal name: the expansion leaves periods alone).
pub const NATURAL: &str = "#natural";

/// `display.Screen(…)` → `Screen`, `display.Digits(…)` → `Digits`.
fn display_type(ty: &Expr) -> Option<&'static str> {
    let ExprKind::Call { func, .. } = &ty.kind else { return None };
    let ExprKind::Attr(b, a) = &func.kind else { return None };
    if !matches!(&b.kind, ExprKind::Name(n) if n == "display") {
        return None;
    }
    match a.as_str() {
        "Screen" => Some("Screen"),
        "Digits" => Some("Digits"),
        _ => None,
    }
}

/// The colour of a readout unless it says: amber, like an old LED display.
const DIGITS_COLOUR: i64 = 0xFF8C00;

/// `output x: display.Digits(n, colour=c)`: the readout's screen (`n` glyphs 4 pixels apart, 5
/// tall) and colour.
fn digits(
    dir: PortDir,
    name: &str,
    ty: &Expr,
    has_signal: bool,
    label: Option<&Expr>,
    consts: &HashMap<String, Cv>,
    span: Span,
) -> Result<(Screen, Expr), Diag> {
    if dir != PortDir::Output {
        return Err(Diag::error(span, "a readout is an `output`"));
    }
    if has_signal {
        return Err(Diag::error(span, "a readout has no `@ signal`: it shows its number on lamps"));
    }
    let ExprKind::Call { args, kwargs, .. } = &ty.kind else { unreachable!() };
    let usage = "expected `display.Digits(digits)` or `display.Digits(digits, colour=0xRRGGBB)`";
    if args.len() != 1 || kwargs.iter().any(|(k, _)| k != "colour" && k != "color") {
        return Err(Diag::error(ty.span, usage));
    }
    let n = match crate::program::eval_const(&args[0], consts, &[]).ok().and_then(|v| v.int()) {
        Some(k) if (1..=10).contains(&k) => k as usize,
        _ => return Err(Diag::error(args[0].span, "a readout has 1 to 10 digits (a constant)")),
    };
    let colour = match kwargs.first() {
        None => int(DIGITS_COLOUR, ty.span),
        Some((_, e)) => match crate::program::eval_const(e, consts, &[]).ok().and_then(|v| v.int()) {
            Some(c) => int(c as i64, e.span),
            None => return Err(Diag::error(e.span, "a readout's colour must be a constant")),
        },
    };
    let label = port_label(label)?;
    let sc = Screen { name: name.to_string(), var: format!("_digits_{name}"), kind: ScreenKind::Digits, w: 4 * n - 1, h: 5, label, span };
    Ok((sc, colour))
}

fn port_label(label: Option<&Expr>) -> Result<Option<String>, Diag> {
    match label {
        None => Ok(None),
        Some(Expr { kind: ExprKind::Call { func, args, .. }, .. })
            if matches!(&func.kind, ExprKind::Name(n) if n == "port") && matches!(args.first().map(|a| &a.kind), Some(ExprKind::Str(_))) =>
        {
            let ExprKind::Str(text) = &args[0].kind else { unreachable!() };
            Ok(Some(text.clone()))
        }
        Some(e) => Err(Diag::error(e.span, "expected `port(\"label\")`")),
    }
}

fn screen(
    dir: PortDir,
    name: &str,
    ty: &Expr,
    has_signal: bool,
    label: Option<&Expr>,
    consts: &HashMap<String, Cv>,
    span: Span,
) -> Result<Screen, Diag> {
    if dir != PortDir::Output {
        return Err(Diag::error(span, "a screen is an `output`"));
    }
    if has_signal {
        return Err(Diag::error(span, "a screen has no `@ signal`: each pixel has its own"));
    }
    let ExprKind::Call { args, kwargs, .. } = &ty.kind else { unreachable!() };
    if args.len() != 2 || !kwargs.is_empty() {
        return Err(Diag::error(ty.span, "expected `display.Screen(width, height)`"));
    }
    let mut dims = Vec::new();
    for a in args {
        match crate::program::eval_const(a, consts, &[]).ok().and_then(|v| v.int()) {
            Some(k) if k > 0 => dims.push(k as usize),
            _ => return Err(Diag::error(a.span, "a screen's width and height must be positive constants")),
        }
    }
    let (w, h) = (dims[0], dims[1]);
    if w * h > MAX_PIXELS {
        return Err(Diag::error(ty.span, format!("a screen can have at most {MAX_PIXELS} pixels; this one has {}", w * h)));
    }
    let label = port_label(label)?;
    Ok(Screen { name: name.to_string(), var: name.to_string(), kind: ScreenKind::Screen, w, h, label, span })
}

fn ex(kind: ExprKind, span: Span) -> Expr {
    Expr { kind, span }
}

fn int(k: i64, span: Span) -> Expr {
    ex(ExprKind::Int(k), span)
}

fn bin(op: BinOp, a: Expr, b: Expr, span: Span) -> Expr {
    ex(ExprKind::Binary(op, Box::new(a), Box::new(b)), span)
}

fn screen_of<'a>(e: &Expr, screens: &'a HashMap<String, Screen>) -> Option<&'a Screen> {
    match &e.kind {
        ExprKind::Name(n) => screens.get(n),
        _ => None,
    }
}

/// Rewrites a body, replacing drawing calls (`screen.rect(…)`, …) with the statements that
/// draw.
fn rewrite_body(b: &mut Vec<Stmt>, screens: &HashMap<String, Screen>, errs: &mut Vec<Diag>) {
    let mut out = Vec::new();
    for mut s in std::mem::take(b) {
        if let Some(stmts) = drawing(&s, screens, errs) {
            out.extend(stmts);
            continue;
        }
        rewrite_stmt(&mut s, screens, errs);
        out.push(s);
    }
    *b = out;
}

/// Drawing calls on screens; `None` for other statements.
fn drawing(s: &Stmt, screens: &HashMap<String, Screen>, errs: &mut Vec<Diag>) -> Option<Vec<Stmt>> {
    let StmtKind::Expr(Expr { kind: ExprKind::Call { func, args, kwargs }, span }) = &s.kind else { return None };
    let ExprKind::Attr(base, m) = &func.kind else { return None };
    let sc = screen_of(base, screens)?;
    let sp = *span;
    let usage = match m.as_str() {
        "rect" => "screen.rect(x, y, width, height, colour)",
        "hline" => "screen.hline(x, y, width, colour)",
        "vline" => "screen.vline(x, y, height, colour)",
        "digit" => "screen.digit(x, y, digit, colour)",
        "number" => "screen.number(x, y, n, colour, width=k)",
        "text" => "screen.text(x, y, \"TEXT\", colour)",
        _ => return None,
    };
    let want = match m.as_str() {
        "rect" => 5,
        "text" | "hline" | "vline" | "digit" | "number" => 4,
        _ => unreachable!(),
    };
    let width_kw = m == "number" && kwargs.iter().all(|(k, _)| k == "width") && kwargs.len() == 1;
    if args.len() != want || !(kwargs.is_empty() || width_kw) || (m == "number" && !width_kw) {
        errs.push(Diag::error(sp, format!("expected `{usage}`")));
        return Some(vec![]);
    }
    let mut args: Vec<Expr> = args.to_vec();
    for a in &mut args {
        rewrite_expr(a, screens, errs);
    }
    // Runtime arguments are evaluated once, into temporaries.
    let mut out = Vec::new();
    let id = DRAW_ID.with(|c| {
        c.set(c.get() + 1);
        c.get()
    });
    let temp = |e: Expr, what: &str, out: &mut Vec<Stmt>| -> Expr {
        if matches!(e.kind, ExprKind::Int(_) | ExprKind::Str(_) | ExprKind::Name(_)) {
            return e;
        }
        let n = format!("_draw{id}_{what}");
        out.push(Stmt { kind: StmtKind::Assign { targets: vec![ex(ExprKind::Name(n.clone()), sp)], value: e }, span: sp });
        ex(ExprKind::Name(n), sp)
    };
    let x = temp(args[0].clone(), "x", &mut out);
    let y = temp(args[1].clone(), "y", &mut out);
    let c = temp(args[want - 1].clone(), "c", &mut out);
    let screen = (**base).clone();
    let draw = |op: i64, rest: Vec<Expr>| -> Stmt {
        let mut a = vec![screen.clone(), int(sc.w as i64, sp), int(op, sp)];
        a.extend(rest);
        let call = ex(ExprKind::Call { func: Box::new(ex(ExprKind::Name("#draw".into()), sp)), args: a, kwargs: vec![] }, sp);
        Stmt { kind: StmtKind::Assign { targets: vec![screen.clone()], value: call }, span: sp }
    };
    let plus = |e: &Expr, k: i64| if k == 0 { e.clone() } else { bin(BinOp::Add, e.clone(), int(k, sp), sp) };
    let glyph_table = |codes: Vec<i32>| ex(ExprKind::List(codes.into_iter().map(|g| int(g as i64, sp)).collect()), sp);
    let digits: Vec<i32> = ('0'..='9').map(|d| glyph(d).unwrap()).collect();
    match m.as_str() {
        "rect" | "hline" | "vline" => {
            let (w, h) = match m.as_str() {
                "rect" => (temp(args[2].clone(), "w", &mut out), temp(args[3].clone(), "h", &mut out)),
                "hline" => (temp(args[2].clone(), "w", &mut out), int(1, sp)),
                _ => (int(1, sp), temp(args[2].clone(), "h", &mut out)),
            };
            out.push(draw(0, vec![x, y, w, h, c]));
        }
        "digit" => {
            let d = temp(args[2].clone(), "d", &mut out);
            let bits = ex(ExprKind::Index(Box::new(glyph_table(digits)), Box::new(d)), sp);
            let bits = temp(bits, "g", &mut out);
            out.push(draw(1, vec![c, x, y, bits]));
        }
        "text" => {
            let ExprKind::Str(text) = &args[2].kind else {
                errs.push(Diag::error(args[2].span, "the text must be a constant string"));
                return Some(vec![]);
            };
            let mut rest = vec![c.clone()];
            for (i, ch) in text.chars().enumerate() {
                let Some(bits) = glyph(ch) else {
                    errs.push(Diag::error(args[2].span, format!("the font has no `{ch}`")).with_help(format!("it has letters, digits, space and {}", font_chars().trim_start_matches(|c: char| c.is_ascii_alphanumeric()))));
                    return Some(vec![]);
                };
                if bits != 0 {
                    rest.extend([plus(&x, 4 * i as i64), y.clone(), int(bits as i64, sp)]);
                }
            }
            out.push(draw(1, rest));
        }
        "number" => {
            let k = match kwargs[0].1.kind {
                ExprKind::Int(k) if (1..=10).contains(&k) => k as usize,
                _ => {
                    errs.push(Diag::error(kwargs[0].1.span, "`width` must be a constant number of digits, 1 to 10"));
                    return Some(vec![]);
                }
            };
            // At a constant position: every pixel's place value is known, so the whole
            // number is worked out at once (`lower_draw`, op 2).
            if let (Some(x0), Some(y0)) = (const_int(&x), const_int(&y)) {
                let n = temp(args[2].clone(), "n", &mut out);
                out.push(draw(2, vec![c, int(x0, sp), int(y0, sp), n, int(k as i64, sp)]));
                return Some(out);
            }
            // Glyphs 0–9, then blank, minus and the overflow mark (every pixel lit).
            let mut codes = digits;
            codes.extend([0, glyph('-').unwrap(), FULL]);
            let n = temp(args[2].clone(), "n", &mut out);
            let nm = |what: &str| format!("_draw{id}_{what}");
            let name_e = |what: &str| ex(ExprKind::Name(nm(what)), sp);
            let assign = |what: &str, e: Expr| Stmt { kind: StmtKind::Assign { targets: vec![name_e(what)], value: e }, span: sp };
            let call = |f: &str, a: Vec<Expr>| ex(ExprKind::Call { func: Box::new(ex(ExprKind::Name(f.into()), sp)), args: a, kwargs: vec![] }, sp);
            let cmp = |a: Expr, op: CmpOp, b: Expr| ex(ExprKind::Compare(Box::new(a), vec![(op, b)]), sp);
            let and = |a: Expr, b: Expr| ex(ExprKind::BoolOp(BoolOp::And, vec![a, b]), sp);
            let or = |a: Expr, b: Expr| ex(ExprKind::BoolOp(BoolOp::Or, vec![a, b]), sp);
            let ifexp = |c: Expr, a: Expr, b: Expr| ex(ExprKind::IfExp { cond: Box::new(c), then: Box::new(a), orelse: Box::new(b) }, sp);
            let pow10 = |i: usize| int(10i64.pow(i as u32), sp);
            out.push(assign("a", call("abs", vec![n.clone()])));
            out.push(assign("neg", cmp(n.clone(), CmpOp::Lt, int(0, sp))));
            let over = or(cmp(name_e("a"), CmpOp::Ge, pow10(k)), and(name_e("neg"), cmp(name_e("a"), CmpOp::Ge, pow10(k - 1))));
            out.push(assign("over", over));
            let mut rest = vec![c.clone()];
            for i in 0..k {
                // (`a` isn't negative: truncating division is enough.)
                let digit = if i == 0 {
                    call("tmod", vec![name_e("a"), int(10, sp)])
                } else {
                    call("tmod", vec![call("tdiv", vec![name_e("a"), pow10(i)]), int(10, sp)])
                };
                // Leading positions have digit 0: blank is 10 more, and the minus sign (just
                // before the first digit) 11 more.
                let mut idx = if i == 0 {
                    digit
                } else {
                    let below = cmp(name_e("a"), CmpOp::Lt, pow10(i));
                    let minus = and(and(name_e("neg"), cmp(name_e("a"), CmpOp::Ge, pow10(i - 1))), below.clone());
                    let blank = bin(BinOp::Mul, int(10, sp), below, sp);
                    bin(BinOp::Add, bin(BinOp::Add, digit, blank, sp), minus, sp)
                };
                if i == k - 1 {
                    idx = ifexp(name_e("over"), int(12, sp), idx);
                }
                let what = format!("g{i}");
                out.push(assign(&what, ex(ExprKind::Index(Box::new(glyph_table(codes.clone())), Box::new(idx)), sp)));
                rest.extend([plus(&x, 4 * (k - 1 - i) as i64), y.clone(), name_e(&what)]);
            }
            out.push(draw(1, rest));
        }
        _ => unreachable!(),
    }
    Some(out)
}

thread_local! {
    static DRAW_ID: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    /// The module's constants, for drawing calls at constant positions.
    static CONSTS: std::cell::RefCell<HashMap<String, Cv>> = std::cell::RefCell::new(HashMap::new());
}

fn const_int(e: &Expr) -> Option<i64> {
    CONSTS.with(|c| crate::program::eval_const(e, &c.borrow(), &[]).ok().and_then(|v| v.int())).map(|k| k as i64)
}

fn rewrite_stmt(s: &mut Stmt, screens: &HashMap<String, Screen>, errs: &mut Vec<Diag>) {
    // `s.fill(c)` as a statement: every pixel set to `c`.
    if let StmtKind::Expr(Expr { kind: ExprKind::Call { func, args, kwargs }, span }) = &s.kind {
        if let ExprKind::Attr(base, m) = &func.kind {
            if let (Some(sc), "fill") = (screen_of(base, screens), m.as_str()) {
                if args.len() != 1 || !kwargs.is_empty() {
                    errs.push(Diag::error(*span, "expected `screen.fill(colour)`"));
                    return;
                }
                let mut c = args[0].clone();
                rewrite_expr(&mut c, screens, errs);
                let sp = *span;
                let value = bin(BinOp::Mul, ex(ExprKind::List(vec![c]), sp), int(sc.pixels() as i64, sp), sp);
                s.kind = StmtKind::Assign { targets: vec![(**base).clone()], value };
                return;
            }
        }
    }
    let body = |b: &mut Vec<Stmt>, errs: &mut Vec<Diag>| rewrite_body(b, screens, errs);
    match &mut s.kind {
        StmtKind::Assign { targets, value } => {
            for t in targets {
                rewrite_expr(t, screens, errs);
            }
            rewrite_expr(value, screens, errs);
        }
        StmtKind::AugAssign { target, value, .. } => {
            rewrite_expr(target, screens, errs);
            rewrite_expr(value, screens, errs);
        }
        StmtKind::AnnAssign { target, value, .. } => {
            rewrite_expr(target, screens, errs);
            if let Some(v) = value {
                rewrite_expr(v, screens, errs);
            }
        }
        StmtKind::Expr(e) | StmtKind::Assert(e) | StmtKind::WaitUntil(e) | StmtKind::WaitTicks(e) => rewrite_expr(e, screens, errs),
        StmtKind::Return(e) => {
            if let Some(e) = e {
                rewrite_expr(e, screens, errs);
            }
        }
        StmtKind::If { cond, body: b, orelse } => {
            rewrite_expr(cond, screens, errs);
            body(b, errs);
            body(orelse, errs);
        }
        StmtKind::While { cond, body: b } => {
            rewrite_expr(cond, screens, errs);
            body(b, errs);
        }
        StmtKind::For { target, iter, body: b } => {
            rewrite_expr(target, screens, errs);
            rewrite_expr(iter, screens, errs);
            body(b, errs);
        }
        StmtKind::Def { body: b, .. }
        | StmtKind::Every { body: b, .. }
        | StmtKind::Process { body: b, .. }
        | StmtKind::Test { body: b, .. }
        | StmtKind::Block { body: b, .. }
        | StmtKind::Sub { body: b, .. } => body(b, errs),
        StmtKind::TestSet { value, .. } => rewrite_expr(value, screens, errs),
        StmtKind::TestRun { ticks } => rewrite_expr(ticks, screens, errs),
        StmtKind::TestRunUntil { cond, max } => {
            rewrite_expr(cond, screens, errs);
            rewrite_expr(max, screens, errs);
        }
        StmtKind::Port { .. }
        | StmtKind::Import(_)
        | StmtKind::Pass
        | StmtKind::Break
        | StmtKind::Continue
        | StmtKind::Global(_)
        | StmtKind::Exit(_)
        | StmtKind::Call(_) => {}
    }
}

fn rewrite_expr(e: &mut Expr, screens: &HashMap<String, Screen>, errs: &mut Vec<Diag>) {
    let span = e.span;
    match &mut e.kind {
        // `s[x, y]` → `s[y * W + x]`
        ExprKind::Index(base, idx) if screen_of(base, screens).is_some() => {
            let w = screen_of(base, screens).unwrap().w;
            rewrite_expr(idx, screens, errs);
            if let ExprKind::Tuple(xy) = &idx.kind {
                if xy.len() != 2 {
                    errs.push(Diag::error(idx.span, "a pixel is `screen[x, y]` (or `screen[i]`, counting row by row)"));
                    return;
                }
                let (x, y) = (xy[0].clone(), xy[1].clone());
                **idx = bin(BinOp::Add, bin(BinOp::Mul, y, int(w as i64, span), span), x, span);
            }
        }
        ExprKind::Attr(base, a) if screen_of(base, screens).is_some() => {
            let sc = screen_of(base, screens).unwrap();
            match a.as_str() {
                "width" => e.kind = ExprKind::Int(sc.w as i64),
                "height" => e.kind = ExprKind::Int(sc.h as i64),
                "fill" => errs.push(Diag::error(span, "`fill` is a statement: `screen.fill(colour)`")),
                "rect" | "hline" | "vline" | "digit" | "number" | "text" => {
                    errs.push(Diag::error(span, format!("`{a}` is a statement: `screen.{a}(…)`")))
                }
                other => errs.push(Diag::error(span, format!("a screen has no `{other}`")).with_help(
                    "screens have `width`, `height`, `fill`, `rect`, `hline`, `vline`, `digit`, `number` and `text`",
                )),
            }
        }
        ExprKind::Int(_) | ExprKind::Bool(_) | ExprKind::Str(_) | ExprKind::Name(_) => {}
        ExprKind::Unary(_, a) | ExprKind::Not(a) | ExprKind::Attr(a, _) => rewrite_expr(a, screens, errs),
        ExprKind::Binary(_, a, b) | ExprKind::Index(a, b) => {
            rewrite_expr(a, screens, errs);
            rewrite_expr(b, screens, errs);
        }
        ExprKind::Compare(a, rest) => {
            rewrite_expr(a, screens, errs);
            for (_, b) in rest {
                rewrite_expr(b, screens, errs);
            }
        }
        ExprKind::BoolOp(_, xs) | ExprKind::Tuple(xs) | ExprKind::List(xs) => {
            for x in xs {
                rewrite_expr(x, screens, errs);
            }
        }
        ExprKind::IfExp { cond, then, orelse } => {
            rewrite_expr(cond, screens, errs);
            rewrite_expr(then, screens, errs);
            rewrite_expr(orelse, screens, errs);
        }
        ExprKind::Call { func, args, kwargs } => {
            rewrite_expr(func, screens, errs);
            for a in args {
                rewrite_expr(a, screens, errs);
            }
            for (_, a) in kwargs {
                rewrite_expr(a, screens, errs);
            }
        }
        ExprKind::ListComp { elt, target, iter, conds } => {
            rewrite_expr(elt, screens, errs);
            rewrite_expr(target, screens, errs);
            rewrite_expr(iter, screens, errs);
            for c in conds {
                rewrite_expr(c, screens, errs);
            }
        }
        ExprKind::Dict(kvs) => {
            for (k, v) in kvs {
                rewrite_expr(k, screens, errs);
                rewrite_expr(v, screens, errs);
            }
        }
        ExprKind::DictComp { key, value, target, iter, conds } => {
            rewrite_expr(key, screens, errs);
            rewrite_expr(value, screens, errs);
            rewrite_expr(target, screens, errs);
            rewrite_expr(iter, screens, errs);
            for c in conds {
                rewrite_expr(c, screens, errs);
            }
        }
    }
}

// ---------------------------------------------------------------------------- drawing

/// The built-in 3×5 font: each glyph is five rows of three pixels, top to bottom; bit
/// `row * 3 + col` (col 0 at the left) is set where the glyph is lit.
const FONT: &[(char, [&str; 5])] = &[
    ('0', ["###", "#.#", "#.#", "#.#", "###"]),
    ('1', [".#.", "##.", ".#.", ".#.", "###"]),
    ('2', ["###", "..#", "###", "#..", "###"]),
    ('3', ["###", "..#", ".##", "..#", "###"]),
    ('4', ["#.#", "#.#", "###", "..#", "..#"]),
    ('5', ["###", "#..", "###", "..#", "###"]),
    ('6', ["###", "#..", "###", "#.#", "###"]),
    ('7', ["###", "..#", ".#.", ".#.", ".#."]),
    ('8', ["###", "#.#", "###", "#.#", "###"]),
    ('9', ["###", "#.#", "###", "..#", "###"]),
    ('A', [".#.", "#.#", "###", "#.#", "#.#"]),
    ('B', ["##.", "#.#", "##.", "#.#", "##."]),
    ('C', [".##", "#..", "#..", "#..", ".##"]),
    ('D', ["##.", "#.#", "#.#", "#.#", "##."]),
    ('E', ["###", "#..", "##.", "#..", "###"]),
    ('F', ["###", "#..", "##.", "#..", "#.."]),
    ('G', [".##", "#..", "#.#", "#.#", ".##"]),
    ('H', ["#.#", "#.#", "###", "#.#", "#.#"]),
    ('I', ["###", ".#.", ".#.", ".#.", "###"]),
    ('J', ["..#", "..#", "..#", "#.#", ".#."]),
    ('K', ["#.#", "#.#", "##.", "#.#", "#.#"]),
    ('L', ["#..", "#..", "#..", "#..", "###"]),
    ('M', ["#.#", "###", "###", "#.#", "#.#"]),
    ('N', ["##.", "#.#", "#.#", "#.#", "#.#"]),
    ('O', [".#.", "#.#", "#.#", "#.#", ".#."]),
    ('P', ["##.", "#.#", "##.", "#..", "#.."]),
    ('Q', [".#.", "#.#", "#.#", "##.", ".##"]),
    ('R', ["##.", "#.#", "##.", "#.#", "#.#"]),
    ('S', [".##", "#..", ".#.", "..#", "##."]),
    ('T', ["###", ".#.", ".#.", ".#.", ".#."]),
    ('U', ["#.#", "#.#", "#.#", "#.#", "###"]),
    ('V', ["#.#", "#.#", "#.#", "#.#", ".#."]),
    ('W', ["#.#", "#.#", "###", "###", "#.#"]),
    ('X', ["#.#", "#.#", ".#.", "#.#", "#.#"]),
    ('Y', ["#.#", "#.#", ".#.", ".#.", ".#."]),
    ('Z', ["###", "..#", ".#.", "#..", "###"]),
    ('-', ["...", "...", "###", "...", "..."]),
    ('.', ["...", "...", "...", "...", ".#."]),
    (':', ["...", ".#.", "...", ".#.", "..."]),
    ('!', [".#.", ".#.", ".#.", "...", ".#."]),
    ('?', ["##.", "..#", ".#.", "...", ".#."]),
    ('%', ["#.#", "..#", ".#.", "#..", "#.#"]),
    ('/', ["..#", "..#", ".#.", "#..", "#.."]),
    ('+', ["...", ".#.", "###", ".#.", "..."]),
    (' ', ["...", "...", "...", "...", "..."]),
];

/// The 15-bit code of a glyph, if the font has it (letters in either case).
pub fn glyph(ch: char) -> Option<i32> {
    let ch = ch.to_ascii_uppercase();
    let rows = FONT.iter().find(|(c, _)| *c == ch)?.1;
    let mut bits = 0;
    for (r, row) in rows.iter().enumerate() {
        for (c, p) in row.chars().enumerate() {
            if p == '#' {
                bits |= 1 << (r * 3 + c);
            }
        }
    }
    Some(bits)
}

/// The characters [`glyph`] knows, for messages.
fn font_chars() -> String {
    FONT.iter().map(|(c, _)| *c).filter(|c| *c != ' ').collect()
}

/// The number a `Digits` readout shows, read back from its pixels (lit = nonzero), as a
/// player would: `Err` for the overflow mark or anything that isn't a number.
pub fn read_digits(sc: &Screen, px: impl Fn(usize) -> i32) -> Result<i64, String> {
    let n = (sc.w + 1) / 4;
    let mut text = String::new();
    for i in 0..n {
        let mut bits = 0;
        for k in 0..15 {
            if px((k / 3) * sc.w + 4 * i + k % 3) != 0 {
                bits |= 1 << k;
            }
        }
        if bits == FULL {
            return Err(format!("`{}` shows its overflow mark", sc.name));
        }
        match "0123456789- ".chars().find(|c| glyph(*c) == Some(bits)) {
            Some(c) => text.push(c),
            None => return Err(format!("`{}` shows something that isn't a digit", sc.name)),
        }
    }
    let t = text.trim();
    if t.is_empty() {
        return Err(format!("`{}` is blank", sc.name));
    }
    t.parse().map_err(|_| format!("`{}` shows \"{text}\", not a number", sc.name))
}

/// Every pixel lit: the overflow mark of `number`.
const FULL: i32 = (1 << 15) - 1;

/// Larger than any coordinate plus one (bit tricks in [`lower_draw`]).
const BIG: i32 = 1 << 16;

/// `#drawb(bank, off, nb, W, op, …)`: one bank of a screen, pixels `off .. off + nb` of a
/// screen `W` wide, after drawing:
/// - op 0, `x, y, w, h, c`: a filled rectangle;
/// - op 1, `c, x1, y1, bits1, x2, y2, bits2, …`: 3×5 glyphs in colour `c` (bit `row * 3 +
///   col` lit), transparent elsewhere; glyphs mustn't overlap.
///
/// With everything constant but the colour, the pixels are known: ordinary writes, which are
/// combined. Otherwise each shape is a mask (−1 on the pixels to paint) computed for the
/// whole bank at once against tables of each pixel's x and y, a few combinators however
/// large; the masks are added on one wire and painted with two combinators.
pub fn lower_draw(g: &mut crate::ir::Graph, names: &mut dyn crate::lower::Names, args: &[Expr], span: Span) -> Result<crate::ir::V, Diag> {
    use crate::ir::{BLit, BOp, BTerm, FOut, Graph};
    use ticky_factorio::{ArOp, CmpOp};
    type V = crate::ir::V;
    let lit = |e: &Expr| match e.kind {
        ExprKind::Int(k) => k as usize,
        _ => unreachable!("drawing: literal arguments"),
    };
    let (off, nb, w, op) = (lit(&args[1]), lit(&args[2]), lit(&args[3]), lit(&args[4]));
    let bank = crate::lower::expr(g, names, &args[0])?;
    let bank = crate::bundle::bundle(g, bank, args[0].span)?;
    let mut ints = Vec::new();
    for a in &args[5..] {
        let x = crate::lower::expr(g, names, a)?;
        ints.push(crate::bundle::int(g, x, a.span)?);
    }
    let px = |k: usize| ((off + k) % w) as i32;
    let py = |k: usize| ((off + k) / w) as i32;
    if op == 2 {
        let (x0, y0, k) = (lit(&args[6]) as i32, lit(&args[7]) as i32, lit(&args[9]));
        let mask = number_mask(g, off, nb, w, x0, y0, ints[3], k);
        return Ok(paint(g, bank, mask, ints[0], span));
    }
    // Shapes: (x, y, w, h) rectangles or (x, y, bits) glyphs.
    let (c, rects, glyphs): (V, Vec<[V; 4]>, Vec<[V; 3]>) = if op == 0 {
        (ints[4], vec![[ints[0], ints[1], ints[2], ints[3]]], vec![])
    } else {
        (ints[0], vec![], ints[1..].chunks(3).map(|t| [t[0], t[1], t[2]]).collect())
    };
    let konst = |g: &Graph, v: V| g.as_const(v);
    // Known pixels.
    let all_known = rects.iter().all(|r| r.iter().all(|v| konst(g, *v).is_some())) && glyphs.iter().all(|r| r.iter().all(|v| konst(g, *v).is_some()));
    if all_known {
        let mut pixels = Vec::new();
        for r in &rects {
            let [x0, y0, ww, hh] = r.map(|v| konst(g, v).unwrap());
            pixels.extend((0..nb).filter(|&k| (x0..x0.saturating_add(ww)).contains(&px(k)) && (y0..y0.saturating_add(hh)).contains(&py(k))));
        }
        for gl in &glyphs {
            let [x0, y0, bits] = gl.map(|v| konst(g, v).unwrap());
            pixels.extend((0..nb).filter(|&k| {
                let (dx, dy) = (px(k) - x0, py(k) - y0);
                (0..3).contains(&dx) && (0..5).contains(&dy) && bits >> (dy * 3 + dx) & 1 != 0
            }));
        }
        let mut b = bank;
        for k in pixels {
            b = g.bset(b, Graph::slot(k), c);
        }
        return Ok(b);
    }
    let add = |g: &mut Graph, a: V, k: i32| -> V {
        let kv = g.konst(k);
        g.ar(ArOp::Add, a, kv)
    };
    let cond = |op: CmpOp, x: V| BLit { op, a: BOp::Each, b: BOp::Val(x) };
    // Pixels inside a box: `x + 1` tables (never 0, so every pixel is on the wire) give `BIG`
    // where x is in range; added to the `y + 1` table, the y range shifted by `BIG` picks the
    // box (marked `mark`).
    let in_box = |g: &mut Graph, x: V, y: V, bw: V, bh: V, mark: i32| -> BTerm {
        let x0 = add(g, x, 1);
        let x1 = g.ar(ArOp::Add, x0, bw);
        let y0 = add(g, y, 1 + BIG);
        let y1 = g.ar(ArOp::Add, y0, bh);
        let xt = g.bconst((0..nb).map(|k| (Graph::slot(k), px(k) + 1)));
        let in_x = BTerm::Filter(xt, vec![vec![cond(CmpOp::Ge, x0), cond(CmpOp::Lt, x1)]], FOut::Const(BIG));
        let yt = BTerm::K((0..nb).map(|k| (Graph::slot(k), py(k) + 1)).collect());
        let zx = g.bun(vec![in_x, yt]);
        BTerm::Filter(zx, vec![vec![cond(CmpOp::Ge, y0), cond(CmpOp::Lt, y1)]], FOut::Const(mark))
    };
    let mut mask: Vec<BTerm> = Vec::new();
    for r in &rects {
        mask.push(in_box(g, r[0], r[1], r[2], r[3], -1));
    }
    for gl in &glyphs {
        let [x, y, bits] = *gl;
        // A pixel at position i (`row * 3 + col`) of the glyph is lit when bit i of `bits`
        // is: `bits << (31 - i)` is negative.
        let neg = vec![vec![cond(CmpOp::Lt, g.konst(0))]];
        match (konst(g, x), konst(g, y)) {
            (Some(x0), Some(y0)) => {
                let sh: Vec<(ticky_factorio::Sig, i32)> = (0..nb)
                    .filter_map(|k| {
                        let (dx, dy) = (px(k) - x0, py(k) - y0);
                        ((0..3).contains(&dx) && (0..5).contains(&dy)).then(|| (Graph::slot(k), 31 - (dy * 3 + dx)))
                    })
                    .collect();
                if sh.is_empty() {
                    continue;
                }
                let sh = g.bconst(sh);
                let shifted = g.bun(vec![BTerm::RMap(ArOp::Shl, bits, sh)]);
                mask.push(BTerm::Filter(shifted, neg, FOut::Const(-1)));
            }
            _ => {
                // Anywhere: shift amounts `31 + 3y + x - (3 py + px)` from a table (of
                // `3 py + px + 1`, never 0, so every pixel is on the wire), then in the box (2)
                // plus lit (1) is 3.
                let (three, five) = (g.konst(3), g.konst(5));
                let boxed = in_box(g, x, y, three, five, 2);
                let pos = g.bconst((0..nb).map(|k| (Graph::slot(k), py(k) * 3 + px(k) + 1)));
                let sy = g.ar(ArOp::Mul, y, three);
                let s = g.ar(ArOp::Add, sy, x);
                let s31 = add(g, s, 32);
                let amount = g.bun(vec![BTerm::RMap(ArOp::Sub, s31, pos)]);
                let shifted = g.bun(vec![BTerm::RMap(ArOp::Shl, bits, amount)]);
                let bit = BTerm::Filter(shifted, neg, FOut::Const(1));
                let both = g.bun(vec![boxed, bit]);
                let three = g.konst(3);
                mask.push(BTerm::Filter(both, vec![vec![cond(CmpOp::Eq, three)]], FOut::Const(-1)));
            }
        }
    }
    if mask.is_empty() {
        return Ok(bank);
    }
    let mask = g.bun(mask);
    Ok(paint(g, bank, mask, c, span))
}

/// `bank` with colour `c` on the pixels where `mask` is −1: `old − old·[lit] + c·[lit]`,
/// added to the old values by one more combinator (a chain of drawings doesn't copy each
/// earlier one's combinators). On a blank bank, just `c·[lit]`.
fn paint(g: &mut crate::ir::Graph, bank: crate::ir::V, mask: crate::ir::V, c: crate::ir::V, span: Span) -> crate::ir::V {
    use crate::ir::BTerm;
    use ticky_factorio::ArOp;
    let z = g.konst(0);
    let neg_c = g.ar(ArOp::Sub, z, c);
    if g.as_bconst(bank).is_some_and(|b| b.is_empty()) {
        return g.bun(vec![BTerm::Map(ArOp::Mul, mask, neg_c)]);
    }
    let delta = g.bun(vec![BTerm::Zip(ArOp::Mul, bank, mask), BTerm::Map(ArOp::Mul, mask, neg_c)]);
    if matches!(g.op(bank), crate::ir::Op::Bun(_)) {
        return g.bun(vec![BTerm::Zip(ArOp::Add, bank, delta)]);
    }
    crate::bundle::binop(g, ticky_syntax::ast::BinOp::Add, bank, delta, span).expect("bundle sum")
}

/// The mask (−1 on lit pixels) of `n` drawn as `k` glyphs from `(x0, y0)`, for the pixels
/// `off .. off + nb` of a screen `w` wide: every glyph at once. Each pixel's digit is
/// `|n| // 10^i % 10` (`i` its glyph's place) plus 10 if it's a leading blank, 11 for the
/// minus sign and 16 + for the overflow mark; a constant per pixel has bit `31 − d` set when
/// glyph `d` lights it, so shifting it left by the digit leaves it negative exactly then.
#[allow(clippy::too_many_arguments)]
fn number_mask(g: &mut crate::ir::Graph, off: usize, nb: usize, w: usize, x0: i32, y0: i32, n: crate::ir::V, k: usize) -> crate::ir::V {
    use crate::ir::{BLit, BOp, BTerm, FOut, Graph};
    use ticky_factorio::{ArOp, CmpOp, Sig};
    // (pixel slot, place i, bit in the glyph) for the pixels inside the number.
    let mut cells: Vec<(Sig, usize, usize)> = Vec::new();
    for j in 0..nb {
        let (px, py) = (((off + j) % w) as i32 - x0, ((off + j) / w) as i32 - y0);
        if px < 0 || py < 0 || py >= 5 || px >= 4 * k as i32 || px % 4 == 3 {
            continue;
        }
        let place = k - 1 - (px / 4) as usize;
        cells.push((Graph::slot(j), place, (py * 3 + px % 4) as usize));
    }
    if cells.is_empty() {
        return g.bconst([]);
    }
    let codes: Vec<i32> = ('0'..='9').map(|d| glyph(d).unwrap()).chain([0, glyph('-').unwrap()]).collect();
    let lights = |bit: usize| -> i32 {
        let mut m: u32 = 0;
        for (d, code) in codes.iter().enumerate() {
            if code >> bit & 1 != 0 {
                m |= 1 << (31 - d);
            }
        }
        // 16 and up: the overflow mark, every pixel lit.
        for d in 16..=26 {
            m |= 1 << (31 - d);
        }
        m as i32
    };
    let pow = |i: usize| 10i64.pow(i as u32);
    let table = |g: &mut Graph, f: &dyn Fn(usize, usize) -> Option<i32>| g.bconst(cells.iter().filter_map(|&(s, i, b)| Some((s, f(i, b)?))));
    let place = table(g, &|i, _| Some(pow(i) as i32));
    let leading = table(g, &|i, _| (i > 0).then(|| pow(i) as i32));
    let top = table(g, &|i, _| (i == k - 1).then_some(1));
    let lit = table(g, &|_, b| Some(lights(b)));
    let z = g.konst(0);
    let neg = g.cmp(CmpOp::Lt, n, z);
    let minus_n = g.ar(ArOp::Sub, z, n);
    let a = g.mux(neg, minus_n, n);
    // Doesn't fit: |n| ≥ 10^k, or negative with |n| ≥ 10^(k-1).
    let fits_neg = g.konst(pow(k - 1).min(i32::MAX as i64) as i32);
    let big_neg = g.cmp(CmpOp::Ge, a, fits_neg);
    let mut over = g.ar(ArOp::And, neg, big_neg);
    if pow(k) <= i32::MAX as i64 {
        let fits = g.konst(pow(k) as i32);
        let big = g.cmp(CmpOp::Ge, a, fits);
        over = g.ar(ArOp::Or, over, big);
    }
    // The minus sign goes where 10^(i-1) ≤ |n| < 10^i: `place ≤ 10|n|` (−1 when positive).
    let ten = g.konst(10);
    let ten_a = g.ar(ArOp::Mul, a, ten);
    let none = g.konst(-1);
    let minus_lim = g.mux(neg, ten_a, none);
    let cond = |op: CmpOp, x: V| BLit { op, a: BOp::Each, b: BOp::Val(x) };
    type V = crate::ir::V;
    let quot = g.bun(vec![BTerm::RMap(ArOp::Div, a, place)]);
    let digit = g.bun(vec![
        BTerm::Map(ArOp::Mod, quot, ten),
        BTerm::Filter(leading, vec![vec![cond(CmpOp::Gt, a)]], FOut::Const(10)),
        BTerm::Filter(leading, vec![vec![cond(CmpOp::Gt, a), cond(CmpOp::Le, minus_lim)]], FOut::Const(1)),
        BTerm::Filter(top, vec![vec![BLit { op: CmpOp::Ne, a: BOp::Val(over), b: BOp::Val(z) }]], FOut::Const(16)),
    ]);
    let shifted = g.bun(vec![BTerm::Zip(ArOp::Shl, lit, digit)]);
    g.bun(vec![BTerm::Filter(shifted, vec![vec![cond(CmpOp::Lt, z)]], FOut::Const(-1))])
}
