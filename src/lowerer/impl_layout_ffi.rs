impl<'a> IrLowerer<'a> {

    fn lookup_layout_for(&self, expr: &Expr) -> Result<LayoutVerdict, LowerError> {
        match expr {
            Expr::TableCtor { .. } => {
                if let Some(&site_id) = self.shape.sites.get(&expr.id()) {
                    Ok(self.shape.layouts[site_id])
                } else {
                    Ok(LayoutVerdict::default())
                }
            }
            Expr::Identifier { name, .. } => Ok(self.read_var(name)?.layout),
            Expr::Index { obj, .. } => self.lookup_layout_for(obj),
            _ => Ok(LayoutVerdict::default()),
        }
    }

    /// A dotted call lowers straight from the checker's recorded verb
    /// (signal 176 → 177): member, arity, and operand faces were all
    /// decided once upstream — this walk only sequences the operands.
    /// Operands are positional: the verb names the face, `args` carries
    /// the expressions, and both walks read the identical AST slice, so
    /// positions cannot drift. The lone guard is the missing-fact tell:
    /// a checker-accepted dotted call always carries a verb.
    fn lower_ffi_call(
        &mut self,
        call: &Expr,
        args: &[Expr],
        reg: RegId,
    ) -> Result<TypedReg, LowerError> {
        let verb = self
            .shape
            .ffi_verbs
            .get(&call.id())
            .cloned()
            .ok_or_else(|| {
                LowerError(Diagnostic::desync(
                    "Lower Error: a dotted call site carries no resolved verb — \
                     the checker and the lowerer disagree",
                ))
            })?;
        signal!(trace::TRACE_LOWER_FFI_VERB);
        match verb {
            FfiVerb::Load => {
                let path = self.lower_expr(&args[0], None)?;
                let path_reg = pooled_ptr_of(path.reg)?;
                self.emit(Instruction::FfiLoad {
                    target: Reg::new(reg),
                    path: path_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::FfiLib,
                })
            }
            FfiVerb::ArgKind => {
                let lib = self.lower_expr(&args[0], None)?;
                let lib_reg = pooled_ptr_of(lib.reg)?;
                self.emit(Instruction::FfiArgKind {
                    target: Reg::new(reg),
                    lib: lib_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            FfiVerb::Cdef => {
                self.emit(Instruction::LoadNull {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::Ffi,
                })
            }
            FfiVerb::CoroCreate => {
                let lib = self.lower_expr(&args[0], None)?;
                let lib_reg = pooled_ptr_of(lib.reg)?;
                self.emit(Instruction::CoroCreate {
                    target: Reg::new(reg),
                    lib: lib_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            FfiVerb::CoroResume => {
                let handle = self.lower_expr(&args[0], None)?;
                let handle_reg = int_of(handle.reg)?;
                let tbl = self.lower_expr(&args[1], None)?;
                let tbl_reg = ptr_of(tbl.reg)?;
                self.emit(Instruction::CoroResume {
                    target: Reg::new(reg),
                    handle: handle_reg,
                    args: tbl_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            FfiVerb::CoroYield => {
                let value = self.lower_expr(&args[0], None)?;
                let value_reg = int_of(value.reg)?;
                self.emit(Instruction::CoroYield {
                    target: Reg::new(reg),
                    value: value_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            FfiVerb::CoroStatus => {
                let handle = self.lower_expr(&args[0], None)?;
                let handle_reg = int_of(handle.reg)?;
                self.emit(Instruction::CoroStatus {
                    target: Reg::new(reg),
                    handle: handle_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Str(Reg::new(reg)),
                    ty: Ty::Str,
                })
            }
            FfiVerb::CoroClose => {
                let handle = self.lower_expr(&args[0], None)?;
                let handle_reg = int_of(handle.reg)?;
                self.emit(Instruction::CoroClose {
                    target: Reg::new(reg),
                    handle: handle_reg,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            FfiVerb::Drive { base, sym } => {
                let local = self.read_var(&base)?;
                let lib_reg = pooled_ptr_of(local.reg)?;
                let arg = self.lower_expr(&args[0], None)?;
                let arg_reg = ptr_of(arg.reg)?;
                self.emit(Instruction::FfiCall {
                    lib: lib_reg,
                    sym,
                    arg: arg_reg,
                });
                self.emit(Instruction::LoadNull {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::Ffi,
                })
            }
        }
    }
}
