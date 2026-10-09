//! Recursive-descent parser following Python's grammar and operator precedence.

use crate::ast::*;
use crate::diag::{Diag, Span};
use crate::lexer::{lex, Tok, Token};

pub fn parse(src: &str) -> Result<Module, Diag> {
    let toks = lex(src)?;
    let mut p = Parser { toks, pos: 0, in_test: false };
    let mut body = Vec::new();
    while !p.at(&Tok::Eof) {
        body.push(p.statement()?);
    }
    Ok(Module { body })
}

/// Keywords that can never be names.
const KEYWORDS: &[&str] = &[
    "if", "elif", "else", "while", "for", "in", "break", "continue", "pass", "def", "return", "and", "or",
    "not", "is", "True", "False", "global", "assert", "class", "lambda", "yield", "async", "await", "try",
    "except", "raise", "with", "import", "from", "nonlocal", "del", "finally", "None",
];

struct Parser {
    toks: Vec<Token>,
    pos: usize,
    /// Inside a `test` block, where `set` and `run` are statements.
    in_test: bool,
}

type PResult<T> = Result<T, Diag>;

impl Parser {
    fn peek(&self) -> &Tok {
        &self.toks[self.pos].tok
    }

    fn peek_at(&self, n: usize) -> &Tok {
        &self.toks[(self.pos + n).min(self.toks.len() - 1)].tok
    }

    fn span(&self) -> Span {
        self.toks[self.pos].span
    }

    fn prev_span(&self) -> Span {
        self.toks[self.pos.saturating_sub(1)].span
    }

    fn at(&self, t: &Tok) -> bool {
        self.peek() == t
    }

    fn at_op(&self, op: &str) -> bool {
        matches!(self.peek(), Tok::Op(o) if *o == op)
    }

    fn at_kw(&self, kw: &str) -> bool {
        matches!(self.peek(), Tok::Name(n) if n == kw)
    }

    fn bump(&mut self) -> Token {
        let t = self.toks[self.pos].clone();
        if self.pos < self.toks.len() - 1 {
            self.pos += 1;
        }
        t
    }

    fn eat_op(&mut self, op: &str) -> bool {
        if self.at_op(op) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn eat_kw(&mut self, kw: &str) -> bool {
        if self.at_kw(kw) {
            self.bump();
            true
        } else {
            false
        }
    }

    fn describe(t: &Tok) -> String {
        match t {
            Tok::Name(n) => format!("`{n}`"),
            Tok::Int(i) => format!("`{i}`"),
            Tok::Str(_) => "a string".into(),
            Tok::Op(o) => format!("`{o}`"),
            Tok::Newline => "end of line".into(),
            Tok::Indent => "an indented block".into(),
            Tok::Dedent => "end of block".into(),
            Tok::Eof => "end of file".into(),
        }
    }

    fn unexpected(&self, wanted: &str) -> Diag {
        Diag::error(self.span(), format!("expected {wanted}, found {}", Self::describe(self.peek())))
    }

    fn expect_op(&mut self, op: &str) -> PResult<Span> {
        if self.at_op(op) {
            Ok(self.bump().span)
        } else {
            Err(self.unexpected(&format!("`{op}`")))
        }
    }

    fn expect_kw(&mut self, kw: &str) -> PResult<Span> {
        if self.at_kw(kw) {
            Ok(self.bump().span)
        } else {
            Err(self.unexpected(&format!("`{kw}`")))
        }
    }

    fn name(&mut self) -> PResult<(String, Span)> {
        match self.peek().clone() {
            Tok::Name(n) if !KEYWORDS.contains(&n.as_str()) => {
                let s = self.bump().span;
                Ok((n, s))
            }
            _ => Err(self.unexpected("a name")),
        }
    }

    fn end_of_statement(&mut self) -> PResult<()> {
        if self.eat_op(";") && !self.at(&Tok::Newline) {
            // Further statements on the same line are handled by the caller loop; keep simple.
            return Err(Diag::error(self.span(), "only one statement per line is supported"));
        }
        if self.at(&Tok::Newline) {
            self.bump();
            Ok(())
        } else if self.at(&Tok::Eof) || self.at(&Tok::Dedent) {
            Ok(())
        } else {
            Err(self.unexpected("end of line"))
        }
    }

    fn block(&mut self) -> PResult<Vec<Stmt>> {
        self.expect_op(":")?;
        if !self.at(&Tok::Newline) {
            // `if x: y = 1` on one line.
            return Ok(vec![self.simple_statement()?]);
        }
        self.bump();
        if !self.at(&Tok::Indent) {
            return Err(self.unexpected("an indented block"));
        }
        self.bump();
        let mut body = Vec::new();
        while !self.at(&Tok::Dedent) && !self.at(&Tok::Eof) {
            body.push(self.statement()?);
        }
        if self.at(&Tok::Dedent) {
            self.bump();
        }
        Ok(body)
    }

    fn statement(&mut self) -> PResult<Stmt> {
        let start = self.span();
        let kw = match self.peek() {
            Tok::Name(n) => n.clone(),
            Tok::Indent => return Err(Diag::error(start, "unexpected indentation")),
            _ => return self.simple_statement(),
        };
        let kind = match kw.as_str() {
            "if" => {
                self.bump();
                return self.if_rest(start);
            }
            "while" => {
                self.bump();
                let cond = self.expr()?;
                let body = self.block()?;
                StmtKind::While { cond, body }
            }
            "for" => {
                self.bump();
                let target = self.target_list()?;
                self.expect_kw("in")?;
                let iter = self.expr_list()?;
                let body = self.block()?;
                StmtKind::For { target, iter, body }
            }
            "def" => {
                self.bump();
                let (name, _) = self.name()?;
                self.expect_op("(")?;
                let mut params = Vec::new();
                while !self.at_op(")") {
                    let (pname, pspan) = self.name()?;
                    let ann = if self.eat_op(":") { Some(self.expr()?) } else { None };
                    let default = if self.eat_op("=") { Some(self.expr()?) } else { None };
                    params.push(Param { name: pname, ann, default, span: pspan });
                    if !self.eat_op(",") {
                        break;
                    }
                }
                self.expect_op(")")?;
                if self.eat_op("->") {
                    self.expr()?;
                }
                let body = self.block()?;
                StmtKind::Def { name, params, body }
            }
            "input" | "output" if matches!(self.peek_at(1), Tok::Name(_)) && matches!(self.peek_at(2), Tok::Op(":")) => {
                self.bump();
                let dir = if kw == "input" { PortDir::Input } else { PortDir::Output };
                let (name, _) = self.name()?;
                self.expect_op(":")?;
                let ty = self.primary()?;
                let signal = if self.eat_op("@") {
                    let s = self.span();
                    if matches!(self.peek_at(1), Tok::Op("(")) {
                        let e = self.primary()?;
                        let span = e.span;
                        Some((SignalSpec::Expr(e), span))
                    } else {
                    match self.bump().tok {
                        Tok::Name(n) => Some((SignalSpec::Ident(n), s)),
                        Tok::Str(n) => Some((SignalSpec::Exact(n), s)),
                        Tok::Int(i) => Some((SignalSpec::Ident(i.to_string()), s)),
                        _ => return Err(Diag::error(s, "expected a signal name after `@`")),
                    }
                    }
                } else {
                    None
                };
                let label = if self.eat_op("=") { Some(self.expr()?) } else { None };
                self.end_of_statement()?;
                StmtKind::Port { dir, name, ty, signal, label }
            }
            "every" if !matches!(self.peek_at(1), Tok::Op("=" | "(" | "." | "[")) => {
                self.bump();
                let period = if self.at_kw("tick") && matches!(self.peek_at(1), Tok::Op(":")) {
                    self.bump();
                    None
                } else {
                    let e = self.bitor()?;
                    if !self.eat_kw("ticks") && !self.eat_kw("tick") {
                        return Err(self.unexpected("`ticks`"));
                    }
                    Some(e)
                };
                let body = self.block()?;
                StmtKind::Every { period, body }
            }
            "process" if matches!(self.peek_at(1), Tok::Name(_)) && matches!(self.peek_at(2), Tok::Op(":")) => {
                self.bump();
                let (name, _) = self.name()?;
                let body = self.block()?;
                StmtKind::Process { name, body }
            }
            "test" if matches!(self.peek_at(1), Tok::Str(_)) => {
                self.bump();
                let name = match self.bump().tok {
                    Tok::Str(s) => s,
                    _ => unreachable!(),
                };
                let was = std::mem::replace(&mut self.in_test, true);
                let body = self.block();
                self.in_test = was;
                StmtKind::Test { name, body: body? }
            }
            "class" | "lambda" | "yield" | "async" | "await" | "try" | "except" | "raise" | "with" | "import"
            | "from" | "nonlocal" | "del" => {
                return Err(Diag::error(start, format!("`{kw}` is not part of Ticky")));
            }
            _ => return self.simple_statement(),
        };
        Ok(Stmt { kind, span: start.to(self.prev_span()) })
    }

    fn if_rest(&mut self, start: Span) -> PResult<Stmt> {
        let cond = self.expr()?;
        let body = self.block()?;
        let orelse = if self.at_kw("elif") {
            let s = self.bump().span;
            vec![self.if_rest(s)?]
        } else if self.eat_kw("else") {
            self.block()?
        } else {
            vec![]
        };
        Ok(Stmt { kind: StmtKind::If { cond, body, orelse }, span: start.to(self.prev_span()) })
    }

    fn simple_statement(&mut self) -> PResult<Stmt> {
        let start = self.span();
        let kind = if self.eat_kw("pass") {
            StmtKind::Pass
        } else if self.eat_kw("break") {
            StmtKind::Break
        } else if self.eat_kw("continue") {
            StmtKind::Continue
        } else if self.eat_kw("return") {
            if self.at(&Tok::Newline) || self.at(&Tok::Eof) {
                StmtKind::Return(None)
            } else {
                StmtKind::Return(Some(self.expr_list()?))
            }
        } else if self.eat_kw("global") {
            let mut names = vec![self.name()?.0];
            while self.eat_op(",") {
                names.push(self.name()?.0);
            }
            StmtKind::Global(names)
        } else if self.eat_kw("assert") {
            StmtKind::Assert(self.expr()?)
        } else if self.at_kw("wait") && !matches!(self.peek_at(1), Tok::Op("=" | "(" | "." | "[")) {
            self.bump();
            if self.eat_kw("until") {
                StmtKind::WaitUntil(self.expr()?)
            } else {
                let e = self.expr()?;
                // `wait 30 ticks` reads naturally; allow the optional unit.
                let _ = self.eat_kw("ticks") || self.eat_kw("tick");
                StmtKind::WaitTicks(e)
            }
        } else if self.in_test && self.at_kw("set") && matches!(self.peek_at(1), Tok::Name(_)) {
            self.bump();
            let (name, _) = self.name()?;
            self.expect_op("=")?;
            StmtKind::TestSet { name, value: self.expr()? }
        } else if self.in_test && self.at_kw("run") {
            self.bump();
            if self.eat_kw("until") {
                let cond = self.expr()?;
                self.expect_op(",")?;
                self.expect_kw("max")?;
                let max = self.bitor()?;
                let _ = self.eat_kw("ticks") || self.eat_kw("tick");
                StmtKind::TestRunUntil { cond, max }
            } else {
                let ticks = self.bitor()?;
                let _ = self.eat_kw("ticks") || self.eat_kw("tick");
                StmtKind::TestRun { ticks }
            }
        } else {
            let first = self.expr_list()?;
            if self.at_op("=") {
                let mut targets = vec![first];
                let mut value = None;
                while self.eat_op("=") {
                    let e = self.expr_list()?;
                    if self.at_op("=") {
                        targets.push(e);
                    } else {
                        value = Some(e);
                    }
                }
                StmtKind::Assign { targets, value: value.unwrap() }
            } else if self.at_op(":") {
                self.bump();
                let ann = self.expr()?;
                let value = if self.eat_op("=") { Some(self.expr_list()?) } else { None };
                StmtKind::AnnAssign { target: first, ann, value }
            } else if let Some(op) = self.aug_op() {
                self.bump();
                StmtKind::AugAssign { target: first, op, value: self.expr_list()? }
            } else {
                StmtKind::Expr(first)
            }
        };
        let span = start.to(self.prev_span());
        self.end_of_statement()?;
        Ok(Stmt { kind, span })
    }

    fn aug_op(&self) -> Option<BinOp> {
        let Tok::Op(o) = self.peek() else { return None };
        Some(match *o {
            "+=" => BinOp::Add,
            "-=" => BinOp::Sub,
            "*=" => BinOp::Mul,
            "/=" => BinOp::Div,
            "//=" => BinOp::FloorDiv,
            "%=" => BinOp::Mod,
            "**=" => BinOp::Pow,
            "<<=" => BinOp::Shl,
            ">>=" => BinOp::Shr,
            "&=" => BinOp::BitAnd,
            "|=" => BinOp::BitOr,
            "^=" => BinOp::BitXor,
            _ => return None,
        })
    }

    /// `a, b` as a tuple; a single expression otherwise.
    fn expr_list(&mut self) -> PResult<Expr> {
        let first = self.expr()?;
        if !self.at_op(",") {
            return Ok(first);
        }
        let mut items = vec![first];
        while self.eat_op(",") {
            if self.at(&Tok::Newline) || self.at_op("=") || self.at_op(")") || self.at_op(":") {
                break;
            }
            items.push(self.expr()?);
        }
        let span = items[0].span.to(items.last().unwrap().span);
        Ok(Expr { kind: ExprKind::Tuple(items), span })
    }

    fn target_list(&mut self) -> PResult<Expr> {
        let first = self.bitor()?;
        if !self.at_op(",") {
            return Ok(first);
        }
        let mut items = vec![first];
        while self.eat_op(",") {
            if self.at_kw("in") {
                break;
            }
            items.push(self.bitor()?);
        }
        let span = items[0].span.to(items.last().unwrap().span);
        Ok(Expr { kind: ExprKind::Tuple(items), span })
    }

    pub fn expr(&mut self) -> PResult<Expr> {
        let e = self.or_test()?;
        if self.at_kw("if") {
            self.bump();
            let cond = self.or_test()?;
            self.expect_kw("else")?;
            let orelse = self.expr()?;
            let span = e.span.to(orelse.span);
            return Ok(Expr {
                kind: ExprKind::IfExp { cond: Box::new(cond), then: Box::new(e), orelse: Box::new(orelse) },
                span,
            });
        }
        Ok(e)
    }

    fn bool_chain(&mut self, kw: &str, op: BoolOp, next: fn(&mut Self) -> PResult<Expr>) -> PResult<Expr> {
        let first = next(self)?;
        if !self.at_kw(kw) {
            return Ok(first);
        }
        let mut items = vec![first];
        while self.eat_kw(kw) {
            items.push(next(self)?);
        }
        let span = items[0].span.to(items.last().unwrap().span);
        Ok(Expr { kind: ExprKind::BoolOp(op, items), span })
    }

    fn or_test(&mut self) -> PResult<Expr> {
        self.bool_chain("or", BoolOp::Or, Self::and_test)
    }

    fn and_test(&mut self) -> PResult<Expr> {
        self.bool_chain("and", BoolOp::And, Self::not_test)
    }

    fn not_test(&mut self) -> PResult<Expr> {
        if self.at_kw("not") {
            let s = self.bump().span;
            let e = self.not_test()?;
            let span = s.to(e.span);
            return Ok(Expr { kind: ExprKind::Not(Box::new(e)), span });
        }
        self.comparison()
    }

    fn cmp_op(&mut self) -> Option<CmpOp> {
        let op = match self.peek() {
            Tok::Op("<") => CmpOp::Lt,
            Tok::Op(">") => CmpOp::Gt,
            Tok::Op("==") => CmpOp::Eq,
            Tok::Op(">=") => CmpOp::Ge,
            Tok::Op("<=") => CmpOp::Le,
            Tok::Op("!=") => CmpOp::Ne,
            Tok::Name(n) if n == "in" => CmpOp::In,
            Tok::Name(n) if n == "not" && matches!(self.peek_at(1), Tok::Name(m) if m == "in") => {
                self.bump();
                CmpOp::NotIn
            }
            Tok::Name(n) if n == "is" => {
                self.bump();
                return Some(if self.eat_kw("not") { CmpOp::IsNot } else { CmpOp::Is });
            }
            _ => return None,
        };
        self.bump();
        Some(op)
    }

    fn comparison(&mut self) -> PResult<Expr> {
        let first = self.bitor()?;
        let mut rest = Vec::new();
        while let Some(op) = self.cmp_op() {
            rest.push((op, self.bitor()?));
        }
        if rest.is_empty() {
            return Ok(first);
        }
        let span = first.span.to(rest.last().unwrap().1.span);
        Ok(Expr { kind: ExprKind::Compare(Box::new(first), rest), span })
    }

    fn binary_level(&mut self, ops: &[(&str, BinOp)], next: fn(&mut Self) -> PResult<Expr>) -> PResult<Expr> {
        let mut left = next(self)?;
        while let Some(op) = ops.iter().find(|(s, _)| self.at_op(s)).map(|(_, o)| *o) {
            self.bump();
            let right = next(self)?;
            let span = left.span.to(right.span);
            left = Expr { kind: ExprKind::Binary(op, Box::new(left), Box::new(right)), span };
        }
        Ok(left)
    }

    fn bitor(&mut self) -> PResult<Expr> {
        self.binary_level(&[("|", BinOp::BitOr)], Self::bitxor)
    }

    fn bitxor(&mut self) -> PResult<Expr> {
        self.binary_level(&[("^", BinOp::BitXor)], Self::bitand)
    }

    fn bitand(&mut self) -> PResult<Expr> {
        self.binary_level(&[("&", BinOp::BitAnd)], Self::shift)
    }

    fn shift(&mut self) -> PResult<Expr> {
        self.binary_level(&[("<<", BinOp::Shl), (">>", BinOp::Shr)], Self::arith)
    }

    fn arith(&mut self) -> PResult<Expr> {
        self.binary_level(&[("+", BinOp::Add), ("-", BinOp::Sub)], Self::term)
    }

    fn term(&mut self) -> PResult<Expr> {
        self.binary_level(
            &[("*", BinOp::Mul), ("//", BinOp::FloorDiv), ("/", BinOp::Div), ("%", BinOp::Mod)],
            Self::factor,
        )
    }

    fn factor(&mut self) -> PResult<Expr> {
        let op = if self.at_op("-") {
            UnOp::Neg
        } else if self.at_op("+") {
            UnOp::Pos
        } else if self.at_op("~") {
            UnOp::Invert
        } else {
            return self.power();
        };
        let s = self.bump().span;
        let e = self.factor()?;
        let span = s.to(e.span);
        Ok(Expr { kind: ExprKind::Unary(op, Box::new(e)), span })
    }

    fn power(&mut self) -> PResult<Expr> {
        let base = self.primary()?;
        if self.eat_op("**") {
            // Right-associative, and binds tighter than unary minus on its left only.
            let exp = self.factor()?;
            let span = base.span.to(exp.span);
            return Ok(Expr { kind: ExprKind::Binary(BinOp::Pow, Box::new(base), Box::new(exp)), span });
        }
        Ok(base)
    }

    fn primary(&mut self) -> PResult<Expr> {
        let mut e = self.atom()?;
        loop {
            if self.eat_op("(") {
                let mut args = Vec::new();
                let mut kwargs = Vec::new();
                while !self.at_op(")") {
                    if let (Tok::Name(n), Tok::Op("=")) = (self.peek().clone(), self.peek_at(1)) {
                        self.bump();
                        self.bump();
                        kwargs.push((n, self.expr()?));
                    } else {
                        if !kwargs.is_empty() {
                            return Err(Diag::error(self.span(), "positional argument after keyword argument"));
                        }
                        args.push(self.expr()?);
                    }
                    if !self.eat_op(",") {
                        break;
                    }
                }
                let end = self.expect_op(")")?;
                let span = e.span.to(end);
                e = Expr { kind: ExprKind::Call { func: Box::new(e), args, kwargs }, span };
            } else if self.eat_op("[") {
                let idx = self.expr_list()?;
                let end = self.expect_op("]")?;
                let span = e.span.to(end);
                e = Expr { kind: ExprKind::Index(Box::new(e), Box::new(idx)), span };
            } else if self.eat_op(".") {
                let (n, s) = self.name()?;
                let span = e.span.to(s);
                e = Expr { kind: ExprKind::Attr(Box::new(e), n), span };
            } else {
                return Ok(e);
            }
        }
    }

    fn atom(&mut self) -> PResult<Expr> {
        let t = self.bump();
        let span = t.span;
        let kind = match t.tok {
            Tok::Int(v) => ExprKind::Int(v),
            Tok::Str(s) => ExprKind::Str(s),
            Tok::Name(n) if n == "True" => ExprKind::Bool(true),
            Tok::Name(n) if n == "False" => ExprKind::Bool(false),
            Tok::Name(n) if n == "None" => {
                return Err(Diag::error(span, "`None` is not part of Ticky").with_help("use 0 or False"))
            }
            Tok::Name(n) if !KEYWORDS.contains(&n.as_str()) => ExprKind::Name(n),
            Tok::Op("(") => {
                if self.at_op(")") {
                    let end = self.bump().span;
                    return Ok(Expr { kind: ExprKind::Tuple(vec![]), span: span.to(end) });
                }
                let mut e = self.expr_list()?;
                let end = self.expect_op(")")?;
                e.span = span.to(end);
                return Ok(e);
            }
            Tok::Op("[") => {
                let mut items = Vec::new();
                while !self.at_op("]") {
                    items.push(self.expr()?);
                    if items.len() == 1 && self.eat_kw("for") {
                        let target = self.target_list()?;
                        self.expect_kw("in")?;
                        let iter = self.or_test()?;
                        let mut conds = Vec::new();
                        while self.eat_kw("if") {
                            conds.push(self.or_test()?);
                        }
                        let end = self.expect_op("]")?;
                        let elt = items.pop().unwrap();
                        return Ok(Expr {
                            kind: ExprKind::ListComp {
                                elt: Box::new(elt),
                                target: Box::new(target),
                                iter: Box::new(iter),
                                conds,
                            },
                            span: span.to(end),
                        });
                    }
                    if !self.eat_op(",") {
                        break;
                    }
                }
                let end = self.expect_op("]")?;
                return Ok(Expr { kind: ExprKind::List(items), span: span.to(end) });
            }
            Tok::Op("{") => {
                let mut items = Vec::new();
                while !self.at_op("}") {
                    let k = self.expr()?;
                    self.expect_op(":")?;
                    let v = self.expr()?;
                    if items.is_empty() && self.eat_kw("for") {
                        let target = self.target_list()?;
                        self.expect_kw("in")?;
                        let iter = self.or_test()?;
                        let mut conds = Vec::new();
                        while self.eat_kw("if") {
                            conds.push(self.or_test()?);
                        }
                        let end = self.expect_op("}")?;
                        return Ok(Expr {
                            kind: ExprKind::DictComp {
                                key: Box::new(k),
                                value: Box::new(v),
                                target: Box::new(target),
                                iter: Box::new(iter),
                                conds,
                            },
                            span: span.to(end),
                        });
                    }
                    items.push((k, v));
                    if !self.eat_op(",") {
                        break;
                    }
                }
                let end = self.expect_op("}")?;
                return Ok(Expr { kind: ExprKind::Dict(items), span: span.to(end) });
            }
            ref other => {
                self.pos -= 1;
                return Err(Diag::error(span, format!("expected an expression, found {}", Self::describe(other))));
            }
        };
        Ok(Expr { kind, span })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn ok(src: &str) -> Module {
        parse(src).unwrap_or_else(|d| panic!("{}", d.render("t", src)))
    }

    #[test]
    fn precedence() {
        let m = ok("x = 1 + 2 * 3 ** 2\n");
        let StmtKind::Assign { value, .. } = &m.body[0].kind else { panic!() };
        let ExprKind::Binary(BinOp::Add, _, r) = &value.kind else { panic!("{value:?}") };
        let ExprKind::Binary(BinOp::Mul, _, r) = &r.kind else { panic!() };
        assert!(matches!(r.kind, ExprKind::Binary(BinOp::Pow, _, _)));
        let m = ok("y = -2 ** 2\n");
        let StmtKind::Assign { value, .. } = &m.body[0].kind else { panic!() };
        assert!(matches!(value.kind, ExprKind::Unary(UnOp::Neg, _)));
    }

    #[test]
    fn program() {
        let src = r#"
input  charge: int @ A = port("Accumulator %")
output steam_on: bool @ S

every tick:
    if charge < 20:
        steam_on = True
    elif charge > 80:
        steam_on = False

every 30 ticks:
    a, b = b, a + b

test "latch":
    set charge = 10
    run 5 ticks
    assert steam_on
    run until steam_on, max 100 ticks
"#;
        let m = ok(src);
        assert_eq!(m.body.len(), 5);
        assert!(matches!(m.body[2].kind, StmtKind::Every { period: None, .. }));
        let StmtKind::Test { body, .. } = &m.body[4].kind else { panic!() };
        assert!(matches!(body[0].kind, StmtKind::TestSet { .. }));
        assert!(matches!(body[3].kind, StmtKind::TestRunUntil { .. }));
    }

    #[test]
    fn errors_point_at_problem() {
        let src = "x = (1 +\n";
        assert!(parse(src).is_err());
        let d = parse("class Foo:\n    pass\n").unwrap_err();
        assert!(d.message.contains("class"));
    }
}
