#[derive(Debug, Clone)]
pub enum BinOp {
    Add,
    Sub,
    Mul,
    Div,
    IntDiv,
    Mod,
    LessThan,
    GreaterThan,
    LessEq,
    GreaterEq,
    Equal,
    NotEqual,
    And,
    Or,
}

#[derive(Debug, Clone)]
pub enum UnOp {
    Neg,
    Not,
    Len,
}

#[derive(Debug, Clone)]
pub enum CtorKey {
    Const(i64),
    Expr(Expr),
    /// `{ name = v }` — a record field. Lowers to the negative interned
    /// identity of `name` (str_key_of_bytes), stored via the overflow map.
    Str(String),
}

#[derive(Debug, Clone)]
pub enum Expr {
    Integer(i64),
    Float(f64),
    Boolean(bool),
    String(String),
    Nil,
    TableCtor {
        entries: Vec<(CtorKey, Expr)>,
        /// The ctor's birth line — its `{`, stamped at construction
        /// (H5 session 3): attribution rides the node, so the parser's
        /// parse-order `ctor_line_seq` pushes become the asserted
        /// shadow and die in session 4. Line only: ctor cols are
        /// unused today and stay that way.
        line: u32,
    },
    Identifier(String),
    Index {
        obj: Box<Expr>,
        key: Box<Expr>,
    },
    BinaryOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
    },
    UnaryOp {
        op: UnOp,
        expr: Box<Expr>,
    },
    SysAllocCount,
    SysExecCount,
    FfiModule,
    CoroModule,
    Field {
        obj: Box<Expr>,
        name: String,
    },
    Function {
        params: Vec<String>,
        body: Vec<Stmt>,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
    },
}

/// Where a statement was born: the (line, col) of its leading token,
/// stamped at construction (H5) — attribution rides the node, so a
/// desugar copies the stamp instead of pre-pushing counter entries.
/// NOT a byte offset: line/col are what consumers eat, and stamped
/// values are byte-identical to the seq pushes they replaced.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Loc {
    pub line: u32,
    pub col: u32,
}

#[derive(Debug, Clone)]
pub enum Stmt {
    LocalDecl {
        names: Vec<String>,
        exprs: Vec<Expr>,
        loc: Loc,
    },
    Assignment {
        name: String,
        expr: Expr,
        loc: Loc,
    },
    IndexAssign {
        obj: Expr,
        key: Expr,
        value: Expr,
        loc: Loc,
    },
    While {
        condition: Expr,
        body: Vec<Stmt>,
        loc: Loc,
    },
    Do {
        body: Vec<Stmt>,
        loc: Loc,
    },
    If {
        condition: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
        loc: Loc,
    },
    Print {
        exprs: Vec<Expr>,
        loc: Loc,
    },
    Expr {
        expr: Expr,
        loc: Loc,
    },
    Return {
        value: Option<Expr>,
        loc: Loc,
    },
    Break {
        loc: Loc,
    },
}

impl Stmt {
    /// The statement's birth stamp (H5): every variant carries `loc`,
    /// and this is the one read face — a field off the enum is not
    /// spellable, so the accessor keeps the stamp's consumers uniform.
    pub fn loc(&self) -> Loc {
        match self {
            Stmt::LocalDecl { loc, .. }
            | Stmt::Assignment { loc, .. }
            | Stmt::IndexAssign { loc, .. }
            | Stmt::While { loc, .. }
            | Stmt::Do { loc, .. }
            | Stmt::If { loc, .. }
            | Stmt::Print { loc, .. }
            | Stmt::Expr { loc, .. }
            | Stmt::Return { loc, .. }
            | Stmt::Break { loc } => *loc,
        }
    }
}

/// True when a `break` belongs to THIS loop level: recurses into Do/If
/// but not into nested While (a break there binds to the inner loop).
/// One definition, two gates that must agree: the lowerer's fill
/// conversion and the analyzer's Dense promotion both refuse loops whose
/// own body carries a break — a fill loop's body must run to the guard's
/// completion, so a break out of it invalidates the reserve. Pinned by
/// fill_break_two_gates (one loop per path in one lock: the converted
/// twin carries the reserve, the break twin the checked stores).
pub fn has_break(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Break { .. } => true,
        Stmt::Do { body, .. } => has_break(body),
        Stmt::While { .. } => false,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => has_break(then_body) || has_break(else_body),
        _ => false,
    })
}
