//! One traversal engine, many behaviors. `walk_stmt`/`walk_expr` own the
//! children-set of every `Stmt`/`Expr` variant exactly once, exhaustively
//! (no `_` arm — rustc forces the engine to know every variant). A `Visitor`
//! override replaces traversal only by not calling the default recursion;
//! the default is always traverse, never skip. Pass logic stays in its
//! module as trait impls; this file holds traversal and nothing else.

use crate::ast::{CtorKey, Expr, Loc, NodeId, Stmt};

/// One `visit_*` method per `Stmt`/`Expr` variant. Default bodies recurse
/// through `walk_stmt`/`walk_expr` (pre-order: the node, then its children
/// in source order). `Break` is the bail channel — the first error ends the
/// walk, shaped after the shape pass's own `Result<(), ShapeError>` walk.
/// Infallible visitors set `type Break = Infallible` and unwrap — the
/// Result costs nothing at runtime and never carries an error.
pub trait Visitor: Sized {
    type Break;

    /// Pre-order hooks, called by `walk_stmt`/`walk_expr` before dispatching
    /// to the per-variant method. For behavior that applies at *every* node
    /// (identity censuses, fingerprint checks) — one hook instead of 27
    /// stamped overrides.
    fn enter_stmt(&mut self, _stmt: &Stmt) -> Result<(), Self::Break> {
        Ok(())
    }

    fn enter_expr(&mut self, _expr: &Expr) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_local_decl(
        &mut self,
        _names: &[String],
        exprs: &[Expr],
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        for e in exprs {
            walk_expr(self, e)?;
        }
        Ok(())
    }

    fn visit_assignment(
        &mut self,
        _name: &str,
        expr: &Expr,
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        walk_expr(self, expr)
    }

    fn visit_index_assign(
        &mut self,
        obj: &Expr,
        key: &Expr,
        value: &Expr,
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        walk_expr(self, obj)?;
        walk_expr(self, key)?;
        walk_expr(self, value)
    }

    fn visit_while(
        &mut self,
        condition: &Expr,
        body: &[Stmt],
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        walk_expr(self, condition)?;
        walk_stmts(self, body)
    }

    fn visit_do(&mut self, body: &[Stmt], _loc: Loc, _id: NodeId) -> Result<(), Self::Break> {
        walk_stmts(self, body)
    }

    fn visit_if(
        &mut self,
        condition: &Expr,
        then_body: &[Stmt],
        else_body: &[Stmt],
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        walk_expr(self, condition)?;
        walk_stmts(self, then_body)?;
        walk_stmts(self, else_body)
    }

    fn visit_print(&mut self, exprs: &[Expr], _loc: Loc, _id: NodeId) -> Result<(), Self::Break> {
        for e in exprs {
            walk_expr(self, e)?;
        }
        Ok(())
    }

    fn visit_expr_stmt(&mut self, expr: &Expr, _loc: Loc, _id: NodeId) -> Result<(), Self::Break> {
        walk_expr(self, expr)
    }

    fn visit_return(
        &mut self,
        value: Option<&Expr>,
        _loc: Loc,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        if let Some(e) = value {
            walk_expr(self, e)?;
        }
        Ok(())
    }

    fn visit_break(&mut self, _loc: Loc, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_integer(&mut self, _value: i64, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_float(&mut self, _value: f64, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_boolean(&mut self, _value: bool, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_string(&mut self, _value: &str, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_nil(&mut self, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_table_ctor(
        &mut self,
        entries: &[(CtorKey, Expr)],
        _line: u32,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        for (k, v) in entries {
            if let CtorKey::Expr(ke) = k {
                walk_expr(self, ke)?;
            }
            walk_expr(self, v)?;
        }
        Ok(())
    }

    fn visit_identifier(&mut self, _name: &str, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_index(&mut self, obj: &Expr, key: &Expr, _id: NodeId) -> Result<(), Self::Break> {
        walk_expr(self, obj)?;
        walk_expr(self, key)
    }

    fn visit_binary_op(
        &mut self,
        _op: &crate::ast::BinOp,
        left: &Expr,
        right: &Expr,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        walk_expr(self, left)?;
        walk_expr(self, right)
    }

    fn visit_unary_op(
        &mut self,
        _op: &crate::ast::UnOp,
        expr: &Expr,
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        walk_expr(self, expr)
    }

    fn visit_sys_alloc_count(&mut self, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_sys_exec_count(&mut self, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_ffi_module(&mut self, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_async_module(&mut self, _id: NodeId) -> Result<(), Self::Break> {
        Ok(())
    }

    fn visit_field(&mut self, obj: &Expr, _name: &str, _id: NodeId) -> Result<(), Self::Break> {
        walk_expr(self, obj)
    }

    fn visit_function(
        &mut self,
        _params: &[String],
        body: &[Stmt],
        _id: NodeId,
    ) -> Result<(), Self::Break> {
        walk_stmts(self, body)
    }

    fn visit_call(&mut self, callee: &Expr, args: &[Expr], _id: NodeId) -> Result<(), Self::Break> {
        walk_expr(self, callee)?;
        for a in args {
            walk_expr(self, a)?;
        }
        Ok(())
    }
}

pub fn walk_stmts<V: Visitor>(v: &mut V, stmts: &[Stmt]) -> Result<(), V::Break> {
    for s in stmts {
        walk_stmt(v, s)?;
    }
    Ok(())
}

pub fn walk_stmt<V: Visitor>(v: &mut V, stmt: &Stmt) -> Result<(), V::Break> {
    v.enter_stmt(stmt)?;
    match stmt {
        Stmt::LocalDecl {
            names,
            exprs,
            loc,
            id,
        } => v.visit_local_decl(names, exprs, *loc, *id),
        Stmt::Assignment {
            name,
            expr,
            loc,
            id,
        } => v.visit_assignment(name, expr, *loc, *id),
        Stmt::IndexAssign {
            obj,
            key,
            value,
            loc,
            id,
        } => v.visit_index_assign(obj, key, value, *loc, *id),
        Stmt::While {
            condition,
            body,
            loc,
            id,
        } => v.visit_while(condition, body, *loc, *id),
        Stmt::Do { body, loc, id } => v.visit_do(body, *loc, *id),
        Stmt::If {
            condition,
            then_body,
            else_body,
            loc,
            id,
        } => v.visit_if(condition, then_body, else_body, *loc, *id),
        Stmt::Print { exprs, loc, id } => v.visit_print(exprs, *loc, *id),
        Stmt::Expr { expr, loc, id } => v.visit_expr_stmt(expr, *loc, *id),
        Stmt::Return { value, loc, id } => v.visit_return(value.as_ref(), *loc, *id),
        Stmt::Break { loc, id } => v.visit_break(*loc, *id),
    }
}

pub fn walk_expr<V: Visitor>(v: &mut V, expr: &Expr) -> Result<(), V::Break> {
    v.enter_expr(expr)?;
    match expr {
        Expr::Integer { value, id } => v.visit_integer(*value, *id),
        Expr::Float { value, id } => v.visit_float(*value, *id),
        Expr::Boolean { value, id } => v.visit_boolean(*value, *id),
        Expr::String { value, id } => v.visit_string(value, *id),
        Expr::Nil { id } => v.visit_nil(*id),
        Expr::TableCtor { entries, line, id } => v.visit_table_ctor(entries, *line, *id),
        Expr::Identifier { name, id } => v.visit_identifier(name, *id),
        Expr::Index { obj, key, id } => v.visit_index(obj, key, *id),
        Expr::BinaryOp {
            op,
            left,
            right,
            id,
        } => v.visit_binary_op(op, left, right, *id),
        Expr::UnaryOp { op, expr, id } => v.visit_unary_op(op, expr, *id),
        Expr::SysAllocCount { id } => v.visit_sys_alloc_count(*id),
        Expr::SysExecCount { id } => v.visit_sys_exec_count(*id),
        Expr::FfiModule { id } => v.visit_ffi_module(*id),
        Expr::AsyncModule { id } => v.visit_async_module(*id),
        Expr::Field { obj, name, id } => v.visit_field(obj, name, *id),
        Expr::Function { params, body, id } => v.visit_function(params, body, *id),
        Expr::Call { callee, args, id } => v.visit_call(callee, args, *id),
    }
}
