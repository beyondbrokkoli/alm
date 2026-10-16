#[derive(Debug, Clone, PartialEq)]
pub enum StaticType {
    Integer,
    Float,
    Boolean,
    String,
    Table(Box<StaticType>),
    Unknown(usize),
    Ffi,
    FfiLib,
    Any,
}

impl std::fmt::Display for StaticType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            StaticType::Integer => write!(f, "Int"),
            StaticType::Float => write!(f, "Float"),
            StaticType::Boolean => write!(f, "Bool"),
            StaticType::String => write!(f, "String"),
            StaticType::Table(inner) => write!(f, "Table<{}>", inner),
            StaticType::Unknown(_) => write!(f, "?"),
            StaticType::Ffi => write!(f, "Ffi"),
            StaticType::FfiLib => write!(f, "FfiLib"),
            StaticType::Any => write!(f, "Any"),
        }
    }
}

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
    FfiModule,
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
}
