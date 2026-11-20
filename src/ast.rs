use std::sync::atomic::{AtomicU32, Ordering};

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NodeId(pub u32);

impl NodeId {
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
    Concat,
}

#[derive(Debug, Clone)]
pub enum UnOp {
    Neg,
    Not,
    Len,
}

/// A constructor-table key. `Const` is the physical-slot form:
/// `slot` is physical from the moment it exists ([index-base] minted
/// at the parser's ctor seam, never shifted later), and `positional`
/// is provenance only — the P8 cure (REBASE_PLAN.md §1.1): a
/// positional entry and an explicit `[k] = v` behave identically
/// everywhere downstream, so provenance rides a field no consumer
/// may match on to change behavior.
#[derive(Debug, Clone)]
pub enum CtorKey {
    Const { slot: i64, positional: bool },
    Expr(Expr),
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
    AsyncModule {
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
            | Expr::AsyncModule { id }
            | Expr::Field { id, .. }
            | Expr::Function { id, .. }
            | Expr::Call { id, .. } => *id,
        }
    }
}

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

/// A `break` reachable from this block. While bodies are deliberately
/// not descended: a break there targets that while, not any enclosing
/// loop — so `visit_while` overrides to skip, and everything else rides
/// the engine's default traversal.
pub fn has_break(stmts: &[Stmt]) -> bool {
    use crate::visit::{Visitor, walk_stmts};
    use std::convert::Infallible;

    struct BreakFinder(bool);

    impl Visitor for BreakFinder {
        type Break = Infallible;

        fn visit_break(&mut self, _loc: Loc, _id: NodeId) -> Result<(), Self::Break> {
            self.0 = true;
            Ok(())
        }

        fn visit_while(
            &mut self,
            _condition: &Expr,
            _body: &[Stmt],
            _loc: Loc,
            _id: NodeId,
        ) -> Result<(), Self::Break> {
            Ok(()) // a break inside targets this while — not an outer one
        }

        fn visit_function(
            &mut self,
            _params: &[String],
            _body: &[Stmt],
            _id: NodeId,
        ) -> Result<(), Self::Break> {
            Ok(()) // a function body has no break of this loop to find
        }
    }

    let mut f = BreakFinder(false);
    let _ = walk_stmts(&mut f, stmts);
    f.0
}
