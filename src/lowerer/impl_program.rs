impl<'a> IrLowerer<'a> {

    pub fn lower_program(&mut self, stmts: &[Stmt]) -> IrProgram {
        let args_reg = self.next_reg();
        self.emit(Instruction::BindArgs {
            target: Reg::new(args_reg),
        });
        self.push_dbg_bind("arg", AnyReg::Ptr(Reg::new(args_reg)), Some(1));
        self.scopes[0].insert(
            "arg".to_string(),
            Local {
                reg: AnyReg::Ptr(Reg::new(args_reg)),
                ty: Ty::Tbl(Box::new(
                    self.shape.boundary_elem.clone().unwrap_or(Ty::Unknown(0)),
                )),
                layout: LayoutVerdict::default(),
            },
        );
        self.return_ctxs.push(ReturnCtx {
            kind: ReturnKind::Boundary,
            exit: None,
            args: Vec::new(),
        });
        for stmt in stmts {
            match self.lower_stmt(stmt) {
                Ok(_) => {}
                Err(e) => {
                    let desync = e.is_desync();
                    // the site-stamp: the stmt's own line off its own
                    // loc (H6: no map — the stamp rides the node)
                    self.diagnostics
                        .push(e.0.with_site(Some(stmt.loc().line as usize)));
                    signal!(trace::TRACE_GHOST_BAIL_LOWERER);
                    if desync {
                        signal!(trace::TRACE_ENG_DESYNC);
                    }
                    break;
                }
            }
        }
        if let Err(e) = self.emit_root_frees() {
            let desync = e.is_desync();
            self.diagnostics.push(e.0);
            signal!(trace::TRACE_GHOST_BAIL_LOWERER);
            if desync {
                signal!(trace::TRACE_ENG_DESYNC);
            }
        }
        if let Err(e) = self.finalize_return_ctx() {
            let desync = e.is_desync();
            self.diagnostics.push(e.0);
            signal!(trace::TRACE_GHOST_BAIL_LOWERER);
            if desync {
                signal!(trace::TRACE_ENG_DESYNC);
            }
        }
        IrProgram {
            blocks: std::mem::take(&mut self.blocks),
            boundary_elem: self.shape.boundary_elem.clone().map(boundary_elem_of),
            entry: crate::ir::EntryKind::Lib,
            source_file: std::path::PathBuf::new(),
        }
    }

    fn zero_reg(&mut self, kind: RegKind) -> AnyReg {
        let r = self.next_reg();
        match kind {
            RegKind::Int => {
                self.emit(Instruction::LoadInt {
                    target: Reg::new(r),
                    val: 0,
                });
                AnyReg::Int(Reg::new(r))
            }
            RegKind::Float => {
                self.emit(Instruction::LoadFloat {
                    target: Reg::new(r),
                    val: 0.0,
                });
                AnyReg::Float(Reg::new(r))
            }
            RegKind::Bool => {
                self.emit(Instruction::LoadBool {
                    target: Reg::new(r),
                    val: false,
                });
                AnyReg::Bool(Reg::new(r))
            }
            RegKind::Ptr => {
                self.emit(Instruction::LoadNull {
                    target: Reg::new(r),
                });
                AnyReg::Ptr(Reg::new(r))
            }
            RegKind::Any => {
                self.emit(Instruction::LoadAnyZero {
                    target: Reg::new(r),
                });
                AnyReg::Any(Reg::new(r))
            }
        }
    }

    fn finalize_return_ctx(&mut self) -> Result<Option<AnyReg>, LowerError> {
        let ctx = self
            .return_ctxs
            .pop()
            .expect("lower_program pushes the root return context");
        let Some(exit) = ctx.exit else {
            if matches!(ctx.kind, ReturnKind::Boundary)
                && self.blocks[self.current_block].terminator.is_none()
            {
                self.terminate(Terminator::Halt);
            }
            let kind = match &ctx.kind {
                ReturnKind::Boundary => RegKind::Ptr,
                ReturnKind::Inline { ty } => repr_of(ty),
            };
            return match ctx.kind {
                ReturnKind::Boundary => Ok(None),
                ReturnKind::Inline { ty } => Ok(Some(string_repr(&ty, self.zero_reg(kind)))),
            };
        };
        let (kind, boundary, ret_ty) = match &ctx.kind {
            ReturnKind::Boundary => (RegKind::Ptr, true, None),
            ReturnKind::Inline { ty } => (repr_of(ty), false, Some(ty)),
        };
        let mut args = ctx.args;
        if self.blocks[self.current_block].terminator.is_none() {
            let fallthrough = if boundary {
                let r = self.next_reg();
                self.emit(Instruction::LoadNull {
                    target: Reg::new(r),
                });
                AnyReg::Ptr(Reg::new(r))
            } else {
                match ret_ty {
                    Some(ty) => string_repr(ty, self.zero_reg(kind)),
                    None => self.zero_reg(kind),
                }
            };
            self.terminate(Terminator::Jump(exit));
            args.push((self.current_block, fallthrough));
        }
        let phi_reg = self.next_reg();
        let phi = phi_of(kind, phi_reg, args)?;
        self.current_block = exit;
        self.emit(Instruction::Phi(phi));
        if boundary {
            self.terminate(Terminator::Return(Reg::new(phi_reg)));
            return Ok(None);
        }
        Ok(Some(match ret_ty {
            Some(ty) => string_repr(ty, kind.reg(phi_reg)),
            None => kind.reg(phi_reg),
        }))
    }
}
