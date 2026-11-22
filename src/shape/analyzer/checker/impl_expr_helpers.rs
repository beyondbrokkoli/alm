use super::super::constraints::UnknownStore;
use super::super::value_call_msg;
use super::Checker;
use super::type_helpers::{bin_op_name, type_name};
use crate::ast::{BinOp, Expr};
use crate::diag::Diagnostic;
use crate::shape::facts::BuiltinVerb;
use crate::shape::ty::Ty;

impl Checker {
    pub(super) fn check_block(&mut self, lat: &mut UnknownStore, stmts: &[crate::ast::Stmt]) {
        for stmt in stmts {
            if let Err(msg) = self.check_stmt(lat, stmt) {
                self.diagnostics
                    .push(msg.with_site(Some(stmt.loc().line as usize)));
                return;
            }
        }
    }

    pub(super) fn numeric_operand(
        &mut self,
        lat: &mut UnknownStore,
        l: &Ty,
        r: &Ty,
        op: &BinOp,
        l_expr: &Expr,
        r_expr: &Expr,
    ) -> Result<Ty, Diagnostic> {
        let (l, r) = self.infer_numeric_pair(lat, l, r)?;
        match (&l, &r) {
            (Ty::Int, Ty::Int) => Ok(Ty::Int),
            (Ty::Flt, Ty::Flt) => Ok(Ty::Flt),
            (Ty::Int, Ty::Flt) | (Ty::Flt, Ty::Int) => Err(Diagnostic::ty(format!(
                "'{}' does not support mixed Integer and Float operands",
                bin_op_name(op)
            ))),
            _ => {
                let note = self
                    .any_provenance_note(lat, &l, l_expr)
                    .or_else(|| self.any_provenance_note(lat, &r, r_expr));
                Err(Diagnostic::ty(format!(
                    "'{}' requires numeric operands{}",
                    bin_op_name(op),
                    note.unwrap_or_default()
                )))
            }
        }
    }

    pub(super) fn is_boundary_chained(&self, lat: &UnknownStore, ty: &Ty) -> bool {
        let seed = lat.boundary_seed();
        matches!(
            (
                lat.resolve(ty),
                lat.resolve(&Ty::Unknown(seed)),
            ),
            (Ty::Unknown(a), Ty::Unknown(b)) if a == b
        )
    }

    pub(super) fn pin_bool(&mut self, lat: &mut UnknownStore, ty: &Ty) -> Result<Ty, Diagnostic> {
        let resolved = lat.resolve(ty);
        if let Ty::Unknown(id) = resolved {
            lat.bind(id, Ty::Bool)?;
            return Ok(Ty::Bool);
        }
        Ok(resolved)
    }

    /// The M2 builtin table: the callee name answered to no user
    /// binding, so assert/error/tonumber get the call. Each verb's arg
    /// laws are checked here, once, and the verb is recorded for the
    /// lowerer to consume straight — the same shape as ffi_verbs.
    pub(super) fn check_builtin_call(
        &mut self,
        lat: &mut UnknownStore,
        expr: &Expr,
        name: &str,
        args: &[Expr],
    ) -> Result<Ty, Diagnostic> {
        let verb = match name {
            "assert" => BuiltinVerb::Assert,
            "error" => BuiltinVerb::Error,
            "tonumber" => BuiltinVerb::ToNumber,
            _ => return Err(value_call_msg(name)),
        };
        let arity = |want: usize| {
            Diagnostic::ty(format!(
                "builtin '{name}' takes {} argument{}, got {}",
                want,
                if want == 1 { "" } else { "s" },
                args.len()
            ))
        };
        match verb {
            BuiltinVerb::Assert => {
                if args.is_empty() || args.len() > 2 {
                    return Err(arity(2));
                }
                let cond = self.check_expr(lat, &args[0])?;
                let cond = self.pin_bool(lat, &cond)?;
                if cond != Ty::Bool {
                    return Err(Diagnostic::ty(format!(
                        "builtin 'assert' checks a Boolean condition — found {} \
                         (the dialect has no coercion; spell the conversion yourself)",
                        type_name(&cond)
                    )));
                }
                if let Some(msg) = args.get(1) {
                    let ty = self.check_expr(lat, msg)?;
                    self.pin_str(lat, &ty, "assert's message")?;
                }
                self.builtin_verbs.insert(expr.id(), BuiltinVerb::Assert);
                Ok(Ty::Bool)
            }
            BuiltinVerb::Error => {
                if !self.stmt_position_call {
                    return Err(Diagnostic::ty(
                        "builtin 'error' raises — it answers no value; call it \
                         as a statement",
                    ));
                }
                if args.len() != 1 {
                    return Err(arity(1));
                }
                let ty = self.check_expr(lat, &args[0])?;
                self.pin_str(lat, &ty, "error's message")?;
                self.builtin_verbs.insert(expr.id(), BuiltinVerb::Error);
                // The raise never answers; the only legal site (a
                // statement) discards the value, so the msg's own type
                // rides home for bookkeeping.
                Ok(Ty::Str)
            }
            BuiltinVerb::ToNumber => {
                if args.len() != 1 {
                    return Err(arity(1));
                }
                let ty = self.check_expr(lat, &args[0])?;
                let ty = self.pin_str(lat, &ty, "tonumber's operand")?;
                if ty != Ty::Str {
                    return Err(Diagnostic::ty(format!(
                        "builtin 'tonumber' parses a String of digits — found {} \
                         (cdata answers wait for ffi.cast)",
                        type_name(&ty)
                    )));
                }
                if let Expr::String { value, .. } = &args[0]
                    && !value.bytes().all(|b| b.is_ascii_digit())
                {
                    return Err(Diagnostic::ty(format!(
                        "builtin 'tonumber' is a digits-only parse — '{value}' \
                         is not all digits"
                    )));
                }
                self.builtin_verbs.insert(expr.id(), BuiltinVerb::ToNumber);
                Ok(Ty::Int)
            }
        }
    }

    /// Pin a type to Str (unknowns bind, everything else must already
    /// be Str) — the shared law of the builtin message/operand lanes.
    pub(super) fn pin_str(
        &mut self,
        lat: &mut UnknownStore,
        ty: &Ty,
        what: &str,
    ) -> Result<Ty, Diagnostic> {
        let resolved = lat.resolve(ty);
        match resolved {
            Ty::Str => Ok(Ty::Str),
            Ty::Unknown(id) => {
                lat.bind(id, Ty::Str)?;
                Ok(Ty::Str)
            }
            other => Err(Diagnostic::ty(format!(
                "{what} is a String — found {} (the dialect has no coercion)",
                type_name(&other)
            ))),
        }
    }

    pub(super) fn infer_numeric_pair(
        &mut self,
        lat: &mut UnknownStore,
        l: &Ty,
        r: &Ty,
    ) -> Result<(Ty, Ty), Diagnostic> {
        let lr = lat.resolve(l);
        let rr = lat.resolve(r);
        let num = |t: &Ty| matches!(t, Ty::Int | Ty::Flt);
        let unknown_id = |t: &Ty| match t {
            Ty::Unknown(id) => *id,
            _ => unreachable!("the pin guards only reach unknowns"),
        };
        let unknown = |t: &Ty| matches!(t, Ty::Unknown(_));
        match (&lr, &rr) {
            (a, b) if num(a) && num(b) => Ok((lr.clone(), rr.clone())),
            (a, b) if num(a) && unknown(b) => {
                lat.bind(unknown_id(b), a.clone())?;
                Ok((a.clone(), a.clone()))
            }
            (a, b) if num(b) && unknown(a) => {
                lat.bind(unknown_id(a), b.clone())?;
                Ok((b.clone(), b.clone()))
            }
            (a, b) if unknown(a) && unknown(b) => {
                lat.bind(unknown_id(a), Ty::Int)?;
                lat.bind(unknown_id(b), Ty::Int)?;
                Ok((Ty::Int, Ty::Int))
            }
            _ => Ok((lr, rr)),
        }
    }

    pub(super) fn pin_scalar_pair(
        &mut self,
        lat: &mut UnknownStore,
        l: &Ty,
        r: &Ty,
    ) -> Result<(), Diagnostic> {
        let lr = lat.resolve(l);
        let rr = lat.resolve(r);
        let scalar = |t: &Ty| matches!(t, Ty::Int | Ty::Flt | Ty::Bool | Ty::Str);
        match (&lr, &rr) {
            (a, Ty::Unknown(id)) if scalar(a) => {
                lat.bind(*id, a.clone())?;
            }
            (Ty::Unknown(id), b) if scalar(b) => {
                lat.bind(*id, b.clone())?;
            }
            _ => {}
        }
        Ok(())
    }

    pub(super) fn any_provenance_note(
        &self,
        lat: &UnknownStore,
        ty: &Ty,
        expr: &Expr,
    ) -> Option<String> {
        if !matches!(lat.resolve(ty), Ty::Any) {
            return None;
        }
        // C: only a plain name or a direct index off one names a value
        // whose provenance a note could adopt
        let name = match expr {
            Expr::Identifier { name: n, .. } => n,
            Expr::Index { obj, .. } => match obj.as_ref() {
                Expr::Identifier { name: n, .. } => n,
                // C: a computed or nested base names nothing adoptable
                _ => return None,
            },
            Expr::Integer { .. }
            | Expr::Float { .. }
            | Expr::Boolean { .. }
            | Expr::String { .. }
            | Expr::Nil { .. }
            | Expr::TableCtor { .. }
            | Expr::BinaryOp { .. }
            | Expr::UnaryOp { .. }
            | Expr::SysAllocCount { .. }
            | Expr::SysExecCount { .. }
            | Expr::FfiModule { .. }
            | Expr::AsyncModule { .. }
            | Expr::Field { .. }
            | Expr::Function { .. }
            | Expr::Call { .. } => return None,
        };
        let line = self.ctx.adopt_lines.get(name)?;
        Some(format!(
            " — '{name}' went dynamic at line {line} (the scalar-kind mix on its cells; \
             adoption is name-global)"
        ))
    }
}
