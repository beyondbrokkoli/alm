use std::sync::atomic::{AtomicU32, Ordering};

/// A node's identity, minted at construction (H6). Until this fold the
/// checker→lowerer contract keyed its fact maps on raw
/// `*const Expr`/`*const Stmt` addresses — an immutability convention
/// ("the AST never moves") with no enforcing type, plus `unsafe`
/// derefs (`FnDef::body`). Identity now rides the node: one
/// construction mints one id, every fact map keys the id, and a
/// node's ADDRESS is nobody's business. A copy of a node IS the node
/// (the id copies with it) — so re-materializing a subtree means
/// CONSTRUCTING, never cloning; the derivation pass's identity census
/// (analysis.rs) panics on any duplicate id reaching the tree, which
/// keeps the law loud instead of conventional.
///
/// `u32` headroom: ~4e9 nodes per process; the mint is a relaxed
/// atomic fetch-add (the compiler is single-threaded; the property
/// harness's parallel test threads only widen uniqueness, which is
/// the safe direction).
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(pub u32);

impl NodeId {
    /// The one minter. Called at every node construction site; there
    /// is no other way an id should exist.
    pub fn mint() -> NodeId {
        static NEXT: AtomicU32 = AtomicU32::new(0);
        NodeId(NEXT.fetch_add(1, Ordering::Relaxed))
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
    /// `{ name = v }` — a record field. Lowers to the negative interned
    /// identity of `name` (str_key_of_bytes), stored via the overflow map.
    Str(String),
}

#[derive(Debug, Clone)]
pub enum Expr {
    Integer {
        value: i64,
        id: NodeId,
    },
    Float {
        value: f64,
        id: NodeId,
    },
    Boolean {
        value: bool,
        id: NodeId,
    },
    String {
        value: String,
        id: NodeId,
    },
    Nil {
        id: NodeId,
    },
    TableCtor {
        entries: Vec<(CtorKey, Expr)>,
        /// The ctor's birth line — its `{`, stamped at construction
        /// (H5): attribution rides the node; there is no parallel
        /// push order to keep in step. Line only: ctor cols are
        /// unused today and stay that way.
        line: u32,
        id: NodeId,
    },
    Identifier {
        name: String,
        id: NodeId,
    },
    Index {
        obj: Box<Expr>,
        key: Box<Expr>,
        id: NodeId,
    },
    BinaryOp {
        op: BinOp,
        left: Box<Expr>,
        right: Box<Expr>,
        id: NodeId,
    },
    UnaryOp {
        op: UnOp,
        expr: Box<Expr>,
        id: NodeId,
    },
    SysAllocCount {
        id: NodeId,
    },
    SysExecCount {
        id: NodeId,
    },
    FfiModule {
        id: NodeId,
    },
    CoroModule {
        id: NodeId,
    },
    Field {
        obj: Box<Expr>,
        name: String,
        id: NodeId,
    },
    Function {
        params: Vec<String>,
        body: Vec<Stmt>,
        id: NodeId,
    },
    Call {
        callee: Box<Expr>,
        args: Vec<Expr>,
        id: NodeId,
    },
}

impl Expr {
    /// The node's identity (H6): every variant carries `id`, minted at
    /// construction — the one read face, twin of `Stmt::loc`'s law (a
    /// field off the enum is not spellable, so fact-map keying stays
    /// uniform over every expression face).
    pub fn id(&self) -> NodeId {
        match self {
            Expr::Integer { id, .. }
            | Expr::Float { id, .. }
            | Expr::Boolean { id, .. }
            | Expr::String { id, .. }
            | Expr::Nil { id }
            | Expr::TableCtor { id, .. }
            | Expr::Identifier { id, .. }
            | Expr::Index { id, .. }
            | Expr::BinaryOp { id, .. }
            | Expr::UnaryOp { id, .. }
            | Expr::SysAllocCount { id }
            | Expr::SysExecCount { id }
            | Expr::FfiModule { id }
            | Expr::CoroModule { id }
            | Expr::Field { id, .. }
            | Expr::Function { id, .. }
            | Expr::Call { id, .. } => *id,
        }
    }
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
        id: NodeId,
    },
    Assignment {
        name: String,
        expr: Expr,
        loc: Loc,
        id: NodeId,
    },
    IndexAssign {
        obj: Expr,
        key: Expr,
        value: Expr,
        loc: Loc,
        id: NodeId,
    },
    While {
        condition: Expr,
        body: Vec<Stmt>,
        loc: Loc,
        id: NodeId,
    },
    Do {
        body: Vec<Stmt>,
        loc: Loc,
        id: NodeId,
    },
    If {
        condition: Expr,
        then_body: Vec<Stmt>,
        else_body: Vec<Stmt>,
        loc: Loc,
        id: NodeId,
    },
    Print {
        exprs: Vec<Expr>,
        loc: Loc,
        id: NodeId,
    },
    Expr {
        expr: Expr,
        loc: Loc,
        id: NodeId,
    },
    Return {
        value: Option<Expr>,
        loc: Loc,
        id: NodeId,
    },
    Break {
        loc: Loc,
        id: NodeId,
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
            | Stmt::Break { loc, .. } => *loc,
        }
    }

    /// The statement's identity (H6), same law as `loc` above.
    pub fn id(&self) -> NodeId {
        match self {
            Stmt::LocalDecl { id, .. }
            | Stmt::Assignment { id, .. }
            | Stmt::IndexAssign { id, .. }
            | Stmt::While { id, .. }
            | Stmt::Do { id, .. }
            | Stmt::If { id, .. }
            | Stmt::Print { id, .. }
            | Stmt::Expr { id, .. }
            | Stmt::Return { id, .. }
            | Stmt::Break { id, .. } => *id,
        }
    }
}

/// True when a `break` belongs to THIS loop level: recurses into Do/If
/// but not into nested While (a break there binds to the inner loop).
/// One definition, one gate (H9 folded the lowerer's second gate into
/// the analyzer's): the fill acceptance predicate that records the
/// FillPlan the lowerer consumes refuses loops whose own body carries
/// a break — a fill loop's body must run to the guard's completion, so
/// a break out of it invalidates the reserve. Pinned by
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
