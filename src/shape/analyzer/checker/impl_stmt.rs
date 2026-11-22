use super::super::constraints::UnknownStore;
use super::type_helpers::type_name;
use super::{Checker, ReturnCtx};
use crate::ast::{Expr, Stmt};
use crate::diag::Diagnostic;
use crate::shape::facts::InstanceId;
use crate::shape::ty::Ty;

impl Checker {
    pub(crate) fn check_stmt(
        &mut self,
        lat: &mut UnknownStore,
        stmt: &Stmt,
    ) -> Result<(), Diagnostic> {
        self.cur_stmt = Some(stmt.id());
        self.cur_stmt_line = Some(stmt.loc().line as usize);
        if self.frames.is_empty() {
            self.cur_decls.clear();
        }
        match stmt {
            Stmt::LocalDecl { names, exprs, .. } => {
                let mut expr_types = Vec::with_capacity(exprs.len());
                for (name, expr) in names.iter().zip(exprs.iter()) {
                    if let Expr::Function { .. } = expr {
                        expr_types.push(self.bind_function(lat, name, expr, false));
                    } else {
                        self.declare_fn_binding(name, None);
                        let ty = self.check_expr(lat, expr)?;
                        Self::reject_face_extraction(expr, &ty)?;
                        expr_types.push(ty);
                    }
                }
                for name in &names[exprs.len()..] {
                    self.declare_fn_binding(name, None);
                }
                for (name, ty) in names.iter().zip(expr_types) {
                    self.declare_var(lat, name.clone(), ty)?;
                }
                for (name, expr) in names.iter().zip(exprs.iter()) {
                    self.track_mint_binding(name, expr);
                }
                for name in &names[exprs.len()..] {
                    let inst = self
                        .instance_stack
                        .first()
                        .copied()
                        .unwrap_or(InstanceId::ROOT);
                    let node = lat.fresh();
                    let id = match node {
                        Ty::Unknown(id) => id,
                        _ => unreachable!("fresh mints an Unknown node"),
                    };
                    self.bare_sites.insert((stmt.id(), inst, name.clone()), id);
                    self.declare_var(lat, name.clone(), Ty::Unknown(id))?;
                }
            }
            Stmt::Assignment { name, expr, .. } => {
                // A write to a captured name is judge-consistent since
                // the Finding B fix: the lowerer routes definer writes
                // to every minted cell of the binding and folds cell
                // writes back into the definer's slot at expansion
                // pop — the register and the cells are one storage at
                // every observation point. The type story rides the
                // monomorphic law: expected (the capture's entry)
                // unifies with actual, so no view goes stale.
                if let Expr::Function { .. } = expr {
                    // an assignment rebinds the binding's home — the
                    // face write follows the rebind law (bind_function's
                    // `rebind` arm); the type bookkeeping below is the
                    // declaration-neutral half and stays as-is
                    let ty = self.bind_function(lat, name, expr, true);
                    if let Some(frame) = self
                        .frames
                        .iter_mut()
                        .rev()
                        .find(|f| f.types.contains_key(name))
                    {
                        frame.types.insert(name.clone(), ty);
                    } else if !self.frames.is_empty() {
                        self.top.insert(name.clone(), ty);
                    } else {
                        self.top.remove(name);
                    }
                    return Ok(());
                }
                self.assign_fn_binding(name, None);
                let expected = self.var_type(lat, name)?;
                let env_hit = self.active_env().is_some_and(|f| f.contains_key(name))
                    || self
                        .env_overrides
                        .last()
                        .is_some_and(|o| o.contains_key(name));
                // (The p5 rejection retired with the p9 reversal: a
                // captured table's binding is cell-backed now, so a
                // closure-side rebind routes through the cell and every
                // holder sees it — the judge's semantics, not a
                // dialect-only law.)
                if matches!(expr, Expr::Nil { .. }) {
                    if !matches!(expected, Ty::Tbl(_) | Ty::Unknown(_)) {
                        return Err(Diagnostic::ty(format!(
                            "'nil' releases tables — '{}' is of type {}",
                            name,
                            type_name(&expected)
                        )));
                    }
                    self.hold_entry(name, expected);
                    self.mint_caps.remove(name);
                    return Ok(());
                }
                let actual = self.check_expr(lat, expr)?;
                Self::reject_face_extraction(expr, &actual)?;
                self.track_mint_binding(name, expr);
                if expected != actual {
                    lat.unify(&expected, &actual)?;
                    let resolved = lat.resolve(&actual);
                    self.write_back(name, resolved);
                }
                if env_hit && let Some(o) = self.env_overrides.last_mut() {
                    o.insert(name.to_string(), lat.resolve(&actual));
                }
            }
            Stmt::IndexAssign {
                obj, key, value, ..
            } => {
                let (elem, _obj_desc) = self.check_index_base(lat, obj)?;
                let _key_ty = self.check_index_key(lat, key)?;
                self.check_mint_bounds(obj, key)?;

                let val_ty = self.check_expr(lat, value)?;

                if matches!(lat.resolve(&val_ty), Ty::Closure(_)) {
                    return Err(Diagnostic::ty(
                        "a closure value enters only a record's literal \
                         fields — computed cells carry scalars and tables",
                    ));
                }

                if matches!(lat.resolve(&elem), Ty::Any) {
                    match lat.resolve(&val_ty) {
                        Ty::Int | Ty::Flt | Ty::Bool | Ty::Str | Ty::Any | Ty::Unknown(_) => {
                            return Ok(());
                        }
                        Ty::Tbl(_) => {
                            return Err(Diagnostic::ty(
                                "an Any table's cells hold scalars — a table value \
                                 cannot enter a dynamic cell",
                            ));
                        }
                        Ty::Ffi | Ty::FfiLib | Ty::Async => {
                            return Err(Diagnostic::ty(
                                "an Any table's cells hold scalars — the ffi \
                                 surface cannot enter a dynamic cell",
                            ));
                        }
                        Ty::Closure(_) => {
                            return Err(Diagnostic::ty(
                                "a closure value enters only a record's literal \
                                 fields — computed cells carry scalars and tables",
                            ));
                        }
                        Ty::Pending | Ty::Conflict => {
                            unreachable!("flow state never rides a resolved checker type")
                        }
                    }
                }

                if matches!(elem, Ty::Tbl(_)) && matches!(val_ty, Ty::Tbl(_)) {
                    let expected_inner = match &elem {
                        Ty::Tbl(inner) => inner.as_ref(),
                        _ => unreachable!(),
                    };
                    let actual_inner = match &val_ty {
                        Ty::Tbl(inner) => inner.as_ref(),
                        _ => unreachable!(),
                    };
                    lat.unify(expected_inner, actual_inner)?;
                } else {
                    lat.unify(&elem, &val_ty)?;
                }
            }
            Stmt::While {
                condition, body, ..
            } => {
                self.check_condition(lat, condition, "while")?;
                self.begin_scope();
                self.loop_depth += 1;
                self.cond_depth += 1;
                self.check_block(lat, body);
                self.cond_depth -= 1;
                self.loop_depth -= 1;
                self.end_scope();
            }
            Stmt::Break { .. } => {
                if self.loop_depth == 0 {
                    return Err(Diagnostic::ty("'break' outside of loop"));
                }
            }
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                self.check_condition(lat, condition, "if")?;
                self.begin_scope();
                self.cond_depth += 1;
                self.check_block(lat, then_body);
                self.cond_depth -= 1;
                self.end_scope();
                self.begin_scope();
                self.cond_depth += 1;
                self.check_block(lat, else_body);
                self.cond_depth -= 1;
                self.end_scope();
            }
            Stmt::Do { body, .. } => {
                self.begin_scope();
                self.check_block(lat, body);
                self.end_scope();
            }
            Stmt::Print { exprs, .. } => {
                for e in exprs {
                    let ty = self.check_expr(lat, e)?;
                    if matches!(ty, Ty::Tbl(_)) {
                        return Err(Diagnostic::ty(
                            "cannot print a table — print its cells instead",
                        ));
                    }
                    if matches!(ty, Ty::Closure(_)) {
                        return Err(Diagnostic::ty(
                            "cannot print a closure — call it, alias it, or \
                             store it in a record field",
                        ));
                    }
                }
            }
            Stmt::Expr { expr, .. } => {
                if matches!(expr, Expr::Call { .. }) {
                    self.stmt_position_call = true;
                }
                if !self.check_ffi_verb(lat, expr)? {
                    let _ = self.check_expr(lat, expr)?;
                }
                self.stmt_position_call = false;
            }
            Stmt::Return { value, .. } => match self.return_ctxs.last().cloned() {
                Some(ReturnCtx::Boundary) => match value {
                    None | Some(Expr::Nil { .. }) => {}
                    Some(expr) => match self.check_expr(lat, expr)? {
                        Ty::Tbl(_) => {
                            if self.carries_closure(expr) {
                                return Err(Diagnostic::ty(
                                    "a closure cannot cross a module boundary — \
                                     the boundary 'return' marshals flat cells only",
                                ));
                            }
                        }
                        other => {
                            return Err(Diagnostic::ty(format!(
                                "'return' hands a value to the host — \
                                     return a table (or nil for null), got {}",
                                type_name(&other)
                            )));
                        }
                    },
                },
                Some(ReturnCtx::Internal(expected)) => {
                    let expr = match value {
                        Some(expr) if !matches!(expr, Expr::Nil { .. }) => expr,
                        _ => {
                            return Err(Diagnostic::ty(
                                "an internal 'return' carries a value — \
                                     the bare and nil forms belong to the script's host \
                                     boundary",
                            ));
                        }
                    };
                    let actual = self.check_expr(lat, expr)?;
                    lat.unify(&expected, &actual)?;
                    let resolved = lat.resolve(&actual);
                    if let Some(ReturnCtx::Internal(ty)) = self.return_ctxs.last_mut() {
                        *ty = resolved;
                    }
                }
                None => unreachable!("new pushes the root return context"),
            },
        }
        Ok(())
    }
}
