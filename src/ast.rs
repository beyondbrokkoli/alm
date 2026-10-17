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
    TableCtor(Vec<(CtorKey, Expr)>),
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

#[derive(Debug, Clone)]
pub enum Stmt {
    LocalDecl {
        names: Vec<String>,
        exprs: Vec<Expr>,
    },
    Assignment {
        name: String,
        expr: Expr,
    },
    IndexAssign {
        obj: Expr,
        key: Expr,
        value: Expr,
    },
    While {
        condition: Expr,
        body: Vec<Stmt>,
    },
    Do {
        body: Vec<Stmt>,
    },
    If {
        condition: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
    },
    Print {
        exprs: Vec<Expr>,
    },
    Expr {
        expr: Expr,
    },
    Return {
        value: Option<Expr>,
    },
    Break,
}

/// True when a `break` belongs to THIS loop level: recurses into Do/If
/// but not into nested While (a break there binds to the inner loop).
/// One definition, two gates that must agree: the lowerer's fill
/// conversion and the analyzer's Dense promotion both refuse loops whose
/// own body carries a break — a fill loop's body must run to the guard's
/// completion, so a break out of it invalidates the reserve.
pub fn has_break(stmts: &[Stmt]) -> bool {
    stmts.iter().any(|s| match s {
        Stmt::Break => true,
        Stmt::Do { body } => has_break(body),
        Stmt::While { .. } => false,
        Stmt::If {
            then_body,
            else_body,
            ..
        } => has_break(then_body) || has_break(else_body),
        _ => false,
    })
}
