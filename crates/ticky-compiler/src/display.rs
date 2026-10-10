//! `import display`: screens made of lamps.
//!
//! `output s: display.Screen(W, H)` is rewritten, before expansion, into an ordinary module
//! variable: a signal array of `W × H` pixels, all 0 to begin with. The compiler keeps it
//! live and shows it on a `W × H` grid of lamps in packed-RGB mode: each lamp shows the low 24
//! bits of its pixel (`0xRRGGBB`), and a pixel of 0 is off. In code, `s[x, y]` is pixel
//! `s[y * W + x]` (row by row from the top left), `s.fill(c)` sets every pixel, and `s.width`
//! / `s.height` are constants.

use std::collections::{HashMap, HashSet};

use ticky_syntax::ast::{BinOp, Expr, ExprKind, Module, PortDir, Stmt, StmtKind};
use ticky_syntax::{Diag, Span};

use crate::ir::Cv;

/// A screen output.
#[derive(Clone, Debug)]
pub struct Screen {
    pub name: String,
    pub w: usize,
    pub h: usize,
    pub label: Option<String>,
    pub span: Span,
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
    let mut body = Vec::new();
    for s in &m.body {
        match &s.kind {
            StmtKind::Import(n) if n == "display" => {
                imported.insert(n.clone());
            }
            StmtKind::Import(n) => errs.push(Diag::error(s.span, format!("there is no library `{n}` (there is `display`)"))),
            StmtKind::Port { dir, name, ty, signal, label } if is_screen_type(ty) => {
                if !imported.contains("display") {
                    errs.push(Diag::error(ty.span, "`display.Screen` needs `import display` first"));
                    continue;
                }
                match screen(*dir, name, ty, signal.is_some(), label.as_ref(), &consts, s.span) {
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
    let by_name: HashMap<String, Screen> = screens.iter().map(|s| (s.name.clone(), s.clone())).collect();
    for s in &mut body {
        rewrite_stmt(s, &by_name, &mut errs);
    }
    if !errs.is_empty() {
        return Err(errs);
    }
    // Every pixel starts at 0 (a prologue value, so every process can read the screen).
    let mut out: Vec<Stmt> = screens
        .iter()
        .map(|sc| {
            let sp = sc.span;
            let zeros = bin(BinOp::Mul, ex(ExprKind::List(vec![int(0, sp)]), sp), int(sc.pixels() as i64, sp), sp);
            Stmt { kind: StmtKind::Assign { targets: vec![ex(ExprKind::Name(sc.name.clone()), sp)], value: zeros }, span: sp }
        })
        .collect();
    out.extend(body);
    Ok((Module { body: out }, screens))
}

fn is_screen_type(ty: &Expr) -> bool {
    match &ty.kind {
        ExprKind::Call { func, .. } => {
            matches!(&func.kind, ExprKind::Attr(b, a) if a == "Screen" && matches!(&b.kind, ExprKind::Name(n) if n == "display"))
        }
        _ => false,
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
    let label = match label {
        None => None,
        Some(Expr { kind: ExprKind::Call { func, args, .. }, .. })
            if matches!(&func.kind, ExprKind::Name(n) if n == "port") && matches!(args.first().map(|a| &a.kind), Some(ExprKind::Str(_))) =>
        {
            let ExprKind::Str(text) = &args[0].kind else { unreachable!() };
            Some(text.clone())
        }
        Some(e) => return Err(Diag::error(e.span, "expected `port(\"label\")`")),
    };
    Ok(Screen { name: name.to_string(), w, h, label, span })
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
    let body = |b: &mut Vec<Stmt>, errs: &mut Vec<Diag>| {
        for s in b {
            rewrite_stmt(s, screens, errs);
        }
    };
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
                other => errs.push(Diag::error(span, format!("a screen has no `{other}` (it has `width`, `height` and `fill`)"))),
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
