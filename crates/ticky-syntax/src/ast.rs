use crate::diag::Span;

#[derive(Clone, Debug)]
pub struct Module {
    pub body: Vec<Stmt>,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug, Hash)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    FloorDiv,
    Mod,
    Pow,
    Shl,
    Shr,
    BitAnd,
    BitOr,
    BitXor,
}

impl BinOp {
    pub fn symbol(self) -> &'static str {
        match self {
            BinOp::Add => "+",
            BinOp::Sub => "-",
            BinOp::Mul => "*",
            BinOp::Div => "/",
            BinOp::FloorDiv => "//",
            BinOp::Mod => "%",
            BinOp::Pow => "**",
            BinOp::Shl => "<<",
            BinOp::Shr => ">>",
            BinOp::BitAnd => "&",
            BinOp::BitOr => "|",
            BinOp::BitXor => "^",
        }
    }
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum UnOp {
    Neg,
    Pos,
    Invert,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum CmpOp {
    Lt,
    Gt,
    Eq,
    Ge,
    Le,
    Ne,
    In,
    NotIn,
    Is,
    IsNot,
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum BoolOp {
    And,
    Or,
}

#[derive(Clone, Debug)]
pub struct Expr {
    pub kind: ExprKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum ExprKind {
    Int(i64),
    Bool(bool),
    Str(String),
    Name(String),
    Unary(UnOp, Box<Expr>),
    Binary(BinOp, Box<Expr>, Box<Expr>),
    Compare(Box<Expr>, Vec<(CmpOp, Expr)>),
    BoolOp(BoolOp, Vec<Expr>),
    Not(Box<Expr>),
    IfExp { cond: Box<Expr>, then: Box<Expr>, orelse: Box<Expr> },
    Call { func: Box<Expr>, args: Vec<Expr>, kwargs: Vec<(String, Expr)> },
    Attr(Box<Expr>, String),
    Index(Box<Expr>, Box<Expr>),
    Tuple(Vec<Expr>),
    List(Vec<Expr>),
    /// `[elt for target in iter if cond…]`
    ListComp { elt: Box<Expr>, target: Box<Expr>, iter: Box<Expr>, conds: Vec<Expr> },
    /// `{key: value, …}`
    Dict(Vec<(Expr, Expr)>),
    /// `{key: value for target in iter if cond…}`
    DictComp { key: Box<Expr>, value: Box<Expr>, target: Box<Expr>, iter: Box<Expr>, conds: Vec<Expr> },
}

#[derive(Copy, Clone, PartialEq, Eq, Debug)]
pub enum PortDir {
    Input,
    Output,
}

#[derive(Clone, Debug)]
pub enum SignalSpec {
    /// `@ iron_plate` — resolved with `_` → `-` and an optional `signal-` prefix.
    Ident(String),
    /// `@ "iron-plate"` — exact prototype name.
    Exact(String),
    /// `@ S("nt-fuel", type="recipe")` — any signal expression.
    Expr(Expr),
}

#[derive(Clone, Debug)]
pub struct Param {
    pub name: String,
    pub ann: Option<Expr>,
    pub default: Option<Expr>,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub struct Stmt {
    pub kind: StmtKind,
    pub span: Span,
}

#[derive(Clone, Debug)]
pub enum StmtKind {
    /// `a = b = value` has two targets.
    Assign { targets: Vec<Expr>, value: Expr },
    AugAssign { target: Expr, op: BinOp, value: Expr },
    AnnAssign { target: Expr, ann: Expr, value: Option<Expr> },
    Expr(Expr),
    Pass,
    Break,
    Continue,
    Return(Option<Expr>),
    Global(Vec<String>),
    Assert(Expr),
    WaitUntil(Expr),
    WaitTicks(Expr),
    /// `elif` chains are nested `If`s in `orelse`.
    If { cond: Expr, body: Vec<Stmt>, orelse: Vec<Stmt> },
    While { cond: Expr, body: Vec<Stmt> },
    For { target: Expr, iter: Expr, body: Vec<Stmt> },
    Def { name: String, params: Vec<Param>, body: Vec<Stmt> },
    Port { dir: PortDir, name: String, ty: Expr, signal: Option<(SignalSpec, Span)>, label: Option<Expr> },
    /// `every tick:` has `period: None`.
    Every { period: Option<Expr>, body: Vec<Stmt> },
    Process { name: String, body: Vec<Stmt> },
    Test { name: String, body: Vec<Stmt> },
    /// `import display`: a library module (only at the top level).
    Import(String),
    /// Test-only: `set port = value`.
    TestSet { name: String, value: Expr },
    /// Test-only: `run N ticks`.
    TestRun { ticks: Expr },
    /// Test-only: `run until cond, max N ticks`.
    TestRunUntil { cond: Expr, max: Expr },
    /// Compiler-internal: a labelled region that `Exit(label)` leaves (inlined function
    /// bodies, unrolled loop iterations).
    Block { label: usize, body: Vec<Stmt> },
    /// Compiler-internal: continue after the end of the enclosing `Block` with this label.
    Exit(usize),
    /// Compiler-internal: call a subroutine (its parameters are already assigned).
    Call(String),
    /// Compiler-internal, top level: a function compiled once and called as a subroutine.
    /// `Exit(label)` inside it returns.
    Sub { name: String, label: usize, body: Vec<Stmt> },
}
