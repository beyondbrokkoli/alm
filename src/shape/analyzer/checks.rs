use super::*;
impl Analyzer {
    pub(super) fn check_table_use(&mut self, rec: Gate, obj: &Expr) -> Result<(), ShapeError> {
        if let Expr::Identifier { name, .. } = obj {
            let (_, bind) = self.resolve(name)?;
            // The rec gate is mirror's law, not a trace artifact: the
            // fixpoint passes tolerate nil/moved reads so the lattice
            // can converge; only the recorded pass refuses them.
            if bind.aliases.contains(&NULL_ROOT) && rec.on() {
                return Err(ShapeError(Diagnostic::lifetime(format!(
                    "'{name}' may be nil here — table reads and \
                     stores through a possibly-nil name are rejected at compile time"
                ))));
            }
            if bind.aliases.contains(&MOVED_ROOT) && rec.on() {
                return Err(ShapeError(Diagnostic::lifetime(format!(
                    "'{name}' may be moved here — table reads and \
                     stores through a possibly-moved name are rejected at compile time"
                ))));
            }
        }
        Ok(())
    }

    pub(super) fn check_len_operand(&mut self, _rec: Gate, expr: &Expr) -> Result<(), ShapeError> {
        if let Expr::Identifier { name, .. } = expr {
            let (_, bind) = self.resolve(name)?;
            if matches!(bind.ty, Str) {
                return Ok(());
            }
            if pinned_scalar(&bind.ty) && !matches!(bind.ty, Pending) {
                return Err(ShapeError(Diagnostic::ty(format!(
                    "'#' requires a Table, String, or Any operand — '{name}' is a \
                     scalar"
                ))));
            }
        }
        Ok(())
    }

    pub(super) fn check_uses(&mut self, rec: Gate, expr: &Expr) -> Result<(), ShapeError> {
        match expr {
            Expr::Identifier { name, .. } => {
                if let Ok((_, bind)) = self.resolve(name)
                    && bind.aliases.contains(&NULL_ROOT)
                {
                    return Err(ShapeError(Diagnostic::lifetime(format!(
                        "'{name}' may be nil here — reads through a \
                         possibly-nil name are rejected at compile time"
                    ))));
                }
                if let Ok((_, bind)) = self.resolve(name)
                    && bind.aliases.contains(&MOVED_ROOT)
                {
                    return Err(ShapeError(Diagnostic::lifetime(format!(
                        "'{name}' may be moved here — reads through a \
                         possibly-moved name are rejected at compile time"
                    ))));
                }
            }
            Expr::TableCtor { entries, .. } => {
                for (key, val) in entries {
                    if let CtorKey::Expr(ke) = key {
                        self.check_uses(rec, ke)?;
                    }
                    self.check_uses(rec, val)?;
                }
            }
            Expr::Index { obj, key, .. } => {
                self.check_table_use(rec, obj)?;
                self.check_uses(rec, obj)?;
                self.check_uses(rec, key)?;
            }
            Expr::UnaryOp { op, expr, .. } => {
                if matches!(op, UnOp::Len) {
                    self.check_table_use(rec, expr)?;
                    self.check_len_operand(rec, expr)?;
                }
                self.check_uses(rec, expr)?;
            }
            Expr::BinaryOp { left, right, .. } => {
                self.check_uses(rec, left)?;
                self.check_uses(rec, right)?;
            }
            Expr::Call { args, .. } => {
                // the callee itself is inference's lane (infer_expr
                // resolves and checks it); only the argument values are
                // use-checked here
                for a in args {
                    self.check_uses(rec, a)?;
                }
            }
            // checked by inference on its own lane: function literals
            // (their bodies walk with the fn frame), Field objects (the
            // receiver's use is checked where the field read is typed),
            // and the leaves carry no names to use
            Expr::Function { .. }
            | Expr::Field { .. }
            | Expr::Integer { .. }
            | Expr::Float { .. }
            | Expr::Boolean { .. }
            | Expr::String { .. }
            | Expr::Nil { .. }
            | Expr::SysAllocCount { .. }
            | Expr::SysExecCount { .. }
            | Expr::FfiModule { .. }
            | Expr::AsyncModule { .. } => {}
        }
        Ok(())
    }
}
