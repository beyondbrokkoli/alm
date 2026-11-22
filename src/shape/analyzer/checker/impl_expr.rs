use super::super::constraints::UnknownStore;
use super::super::{calls_through_fn_var_msg, dotted_callee};
use super::Checker;
use super::type_helpers::{type_name, types_compatible};
use crate::ast::{BinOp, CtorKey, Expr, UnOp};
use crate::diag::Diagnostic;
use crate::shape::ty::Ty;

impl Checker {
    pub(super) fn check_expr(
        &mut self,
        lat: &mut UnknownStore,
        expr: &Expr,
    ) -> Result<Ty, Diagnostic> {
        match expr {
            Expr::Integer { .. } => Ok(Ty::Int),
            Expr::Float { .. } => Ok(Ty::Flt),
            Expr::Boolean { .. } => Ok(Ty::Bool),
            Expr::String { .. } => Ok(Ty::Str),
            Expr::Nil { .. } => Err(Diagnostic::ty(
                "'nil' is only valid as the right-hand side of 't = nil' — \
                 it releases a table's memory, it is not a value",
            )),
            Expr::TableCtor { entries, .. } => {
                let elem = self.elem_of(lat, expr);
                let mut has_int_key = false;
                let mut has_str_key = false;
                for (key, e) in entries {
                    match key {
                        // [P8] provenance is a field: the checker reads
                        // the kind only — `Const { .. }` is an int key
                        // whatever its mint was.
                        CtorKey::Const { .. } => has_int_key = true,
                        CtorKey::Str(_) => has_str_key = true,
                        CtorKey::Expr(ke) => {
                            if self.check_index_key(lat, ke)? == Ty::Str {
                                has_str_key = true;
                            } else {
                                has_int_key = true;
                            }
                        }
                    }
                    if has_int_key && has_str_key {
                        return Err(Diagnostic::ty(
                            "mixed array and record constructor elements — a \
                             constructor is an array or a record, never both",
                        ));
                    }
                    let ty = self.check_expr(lat, e)?;
                    if let Ty::Closure(ptr) = ty {
                        match key {
                            CtorKey::Str(field) => {
                                let Some(&site) = self.ctx.sites.get(&expr.id()) else {
                                    panic!(
                                        "a closure field's constructor carries no \
                                         site — the derivation pass stamps every \
                                         ctor face (H7's face law)",
                                    );
                                };
                                self.closure_fields.insert((site, field.clone()), ptr);
                                continue;
                            }
                            _ => {
                                return Err(Diagnostic::ty(
                                    "a closure value enters only a record's \
                                     literal fields — array cells and computed keys carry \
                                     scalars and tables",
                                ));
                            }
                        }
                    }
                    if matches!(elem, Ty::Tbl(_)) && matches!(ty, Ty::Tbl(_)) {
                        let expected_inner = match &elem {
                            Ty::Tbl(inner) => inner.as_ref(),
                            _ => unreachable!(),
                        };
                        let actual_inner = match &ty {
                            Ty::Tbl(inner) => inner.as_ref(),
                            _ => unreachable!(),
                        };
                        if expected_inner != actual_inner {
                            lat.unify(expected_inner, actual_inner)?;
                        }
                    } else if ty != elem {
                        if matches!(elem, Ty::Any) {
                            if matches!(ty, Ty::Tbl(_)) {
                                return Err(Diagnostic::ty(format!(
                                    "an Any table's cells hold scalars — a table \
                                     value cannot enter a dynamic cell ({} after Any)",
                                    type_name(&ty)
                                )));
                            }
                            if matches!(ty, Ty::Unknown(_)) {
                                lat.unify(&elem, &ty)?;
                            }
                            continue;
                        }
                        lat.unify(&elem, &ty)?;
                        let resolved = lat.resolve(&ty);
                        if resolved != lat.resolve(&elem) {
                            return Err(Diagnostic::ty(format!(
                                "mixed table constructor elements — {} after {}",
                                type_name(&ty),
                                type_name(&elem)
                            )));
                        }
                    }
                }
                let has_closure_field = self
                    .ctx
                    .sites
                    .get(&expr.id())
                    .is_some_and(|s| self.closure_fields.keys().any(|(cs, _)| cs == s));
                if has_closure_field {
                    match lat.resolve(&elem) {
                        Ty::Int | Ty::Flt | Ty::Str | Ty::Unknown(_) | Ty::Pending => {}
                        other => {
                            return Err(Diagnostic::ty(format!(
                                "a closure record's non-closure fields are 8-byte \
                                 scalars (Int/Flt/Str) — its element type is {}",
                                type_name(&other)
                            )));
                        }
                    }
                }
                Ok(Ty::Tbl(Box::new(elem)))
            }
            Expr::Index { obj, key, .. } => {
                let (elem, _) = self.check_index_base(lat, obj)?;
                let _key_ty = self.check_index_key(lat, key)?;
                self.check_mint_bounds(obj, key)?;
                Ok(elem)
            }
            Expr::Identifier { name, .. } => {
                if self.resolves_to_fn(name) {
                    let ptr = self
                        .resolve_fn_binding(name)
                        .flatten()
                        .expect("resolves_to_fn");
                    return self.create_closure(lat, expr, name, ptr);
                }
                self.var_type(lat, name)
            }
            Expr::BinaryOp {
                op, left, right, ..
            } => {
                let l = self.check_expr(lat, left)?;
                let r = self.check_expr(lat, right)?;
                match op {
                    BinOp::Concat => {
                        // '..' is the string lane: Str .. Str -> Str. An
                        // unknown pins to Str (it can only ever join here as
                        // one); anything else — Int, Bool, Any cells — is a
                        // named rejection. Coercion is a later law, if ever.
                        for t in [&l, &r] {
                            let t = lat.resolve(t);
                            match t {
                                Ty::Str => {}
                                Ty::Unknown(id) => {
                                    lat.bind(id, Ty::Str)?;
                                }
                                other => {
                                    return Err(Diagnostic::ty(format!(
                                        "'..' concatenates String with String — \
                                         found {} on one side (the dialect has no \
                                         coercion; spell the conversion yourself)",
                                        type_name(&other)
                                    )));
                                }
                            }
                        }
                        Ok(Ty::Str)
                    }
                    BinOp::And | BinOp::Or => {
                        let l = self.pin_bool(lat, &l)?;
                        let r = self.pin_bool(lat, &r)?;
                        if l == Ty::Bool && r == Ty::Bool {
                            Ok(Ty::Bool)
                        } else {
                            Err(Diagnostic::ty(format!(
                                "'{}' requires Boolean operands on both sides",
                                match op {
                                    BinOp::And => "and",
                                    _ => "or",
                                }
                            )))
                        }
                    }
                    BinOp::Add | BinOp::Sub | BinOp::Mul | BinOp::IntDiv | BinOp::Mod => {
                        self.numeric_operand(lat, &l, &r, op, left, right)
                    }
                    BinOp::Div => {
                        self.infer_numeric_pair(lat, &l, &r)?;
                        let l = lat.resolve(&l);
                        let r = lat.resolve(&r);
                        if !matches!((&l, &r), (Ty::Int | Ty::Flt, Ty::Int | Ty::Flt,)) {
                            let note = self
                                .any_provenance_note(lat, &l, left)
                                .or_else(|| self.any_provenance_note(lat, &r, right));
                            return Err(Diagnostic::ty(format!(
                                "'/' requires numeric operands{}",
                                note.unwrap_or_default()
                            )));
                        }
                        Ok(Ty::Flt)
                    }
                    BinOp::LessThan | BinOp::GreaterThan | BinOp::LessEq | BinOp::GreaterEq => {
                        self.numeric_operand(lat, &l, &r, op, left, right)?;
                        Ok(Ty::Bool)
                    }
                    BinOp::Equal | BinOp::NotEqual => {
                        self.pin_scalar_pair(lat, &l, &r)?;
                        let l = lat.resolve(&l);
                        let r = lat.resolve(&r);
                        if l == Ty::Str && r == Ty::Str {
                            return Ok(Ty::Bool);
                        }
                        if l == Ty::Str || r == Ty::Str {
                            return Err(Diagnostic::ty(format!(
                                "'{}' compares String with {}",
                                match op {
                                    BinOp::Equal => "==",
                                    _ => "~=",
                                },
                                type_name(if l == Ty::Str { &r } else { &l })
                            )));
                        }
                        let l_unk = matches!(l, Ty::Unknown(_));
                        let r_unk = matches!(r, Ty::Unknown(_));
                        if (l_unk && matches!(r, Ty::Tbl(_)) || r_unk && matches!(l, Ty::Tbl(_)))
                            && (self.is_boundary_chained(lat, &l)
                                || self.is_boundary_chained(lat, &r))
                        {
                            return Err(Diagnostic::ty(
                                "'==' compares a boundary cell with a table — \
                                 boundary cells hold scalars",
                            ));
                        }
                        if !types_compatible(&l, &r) {
                            return Err(Diagnostic::ty(format!(
                                "'{}' compares {} with {}",
                                match op {
                                    BinOp::Equal => "==",
                                    _ => "~=",
                                },
                                type_name(&l),
                                type_name(&r)
                            )));
                        }
                        Ok(Ty::Bool)
                    }
                }
            }
            Expr::UnaryOp { op, expr, .. } => {
                let t = self.check_expr(lat, expr)?;
                match op {
                    UnOp::Neg => {
                        let t = lat.resolve(&t);
                        let t = if let Ty::Unknown(id) = t {
                            lat.bind(id, Ty::Int)?;
                            Ty::Int
                        } else {
                            t
                        };
                        match t {
                            Ty::Int | Ty::Flt => Ok(t),
                            _ => Err(Diagnostic::ty("unary '-' requires a numeric operand")),
                        }
                    }
                    UnOp::Not => {
                        let t = self.pin_bool(lat, &t)?;
                        match t {
                            Ty::Bool => Ok(Ty::Bool),
                            _ => Err(Diagnostic::ty("'not' requires a Boolean operand")),
                        }
                    }
                    UnOp::Len => match lat.resolve(&t) {
                        Ty::Tbl(_) | Ty::Str => Ok(Ty::Int),
                        Ty::Any => Ok(Ty::Int),
                        unknown @ Ty::Unknown(_) => {
                            let line = self.cur_stmt_line;
                            self.len_deferrals.push((unknown, line));
                            Ok(Ty::Int)
                        }
                        _ => Err(Diagnostic::ty(format!(
                            "'#' requires a Table, String, or Any operand, got {}",
                            type_name(&t)
                        ))),
                    },
                }
            }
            Expr::SysAllocCount { .. } | Expr::SysExecCount { .. } => Ok(Ty::Int),
            Expr::FfiModule { .. } => Ok(Ty::Ffi),
            Expr::AsyncModule { .. } => Ok(Ty::Async),
            Expr::Field { obj, name, .. } => {
                let ty = self.check_expr(lat, obj)?;
                let ty = lat.resolve(&ty);
                match ty {
                    Ty::Tbl(elem) => {
                        if let Some(ptr) = self.closure_field_fn(obj, name) {
                            self.shadow_pair()
                                .access_elems
                                .insert(obj.id(), Ty::Closure(ptr));
                            return Ok(Ty::Closure(ptr));
                        }
                        self.shadow_pair()
                            .access_elems
                            .insert(obj.id(), (*elem).clone());
                        Ok(*elem)
                    }
                    other => Err(Diagnostic::ty(format!(
                        "dot access needs a record or the ffi surface, got {}",
                        type_name(&other)
                    ))),
                }
            }
            Expr::Function { .. } => Err(Diagnostic::ty(
                "a function value binds directly to a variable — \
                 'local f = function(a, b) ... end'",
            )),
            Expr::Call { callee, args, .. } => {
                let name = match callee.as_ref() {
                    Expr::Identifier { name: n, .. } => n.clone(),
                    Expr::Field { obj, name, .. } => {
                        if let Some(dotted) = dotted_callee(callee.as_ref())
                            && self.resolve_fn_binding(&dotted).is_some()
                        {
                            dotted
                        } else if let Some(ptr) = self.closure_field_fn(obj, name) {
                            self.shadow_pair()
                                .access_elems
                                .insert(obj.id(), Ty::Closure(ptr));
                            self.shadow_pair().closure_calls.insert(expr.id());
                            return self.expand_call(lat, expr, obj, name, ptr, true, args);
                        } else {
                            return self.check_ffi_call(lat, expr, obj, name, args);
                        }
                    }
                    _ => {
                        return Err(calls_through_fn_var_msg());
                    }
                };
                let param_shadows = self
                    .expansion_params
                    .last()
                    .is_some_and(|ps| ps.iter().any(|p| p == &name));
                let fn_ptr = if param_shadows {
                    None
                } else {
                    self.resolve_fn_binding(&name).flatten()
                };
                let (fn_ptr, call_through) = match fn_ptr {
                    Some(ptr) => (ptr, false),
                    None => match self.var_type_callable(lat, &name) {
                        Some(Ty::Closure(ptr)) => (ptr, true),
                        _ => {
                            // The name answers to no user binding — the
                            // M2 builtin table gets the call before the
                            // rejection does.
                            return self.check_builtin_call(lat, expr, &name, args);
                        }
                    },
                };
                self.expand_call(
                    lat,
                    expr,
                    callee.as_ref(),
                    &name,
                    fn_ptr,
                    call_through,
                    args,
                )
            }
        }
    }
}
