impl<'a> IrLowerer<'a> {

    fn lower_expr(&mut self, expr: &Expr, target: Option<RegId>) -> Result<TypedReg, LowerError> {
        let reg = target.unwrap_or_else(|| self.next_reg());

        match expr {
            Expr::Integer { value: val, .. } => {
                self.emit(Instruction::LoadInt {
                    target: Reg::new(reg),
                    val: *val,
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            Expr::Float { value: val, .. } => {
                self.emit(Instruction::LoadFloat {
                    target: Reg::new(reg),
                    val: *val,
                });
                Ok(TypedReg {
                    reg: AnyReg::Float(Reg::new(reg)),
                    ty: Ty::Flt,
                })
            }
            Expr::Boolean { value: val, .. } => {
                self.emit(Instruction::LoadBool {
                    target: Reg::new(reg),
                    val: *val,
                });
                Ok(TypedReg {
                    reg: AnyReg::Bool(Reg::new(reg)),
                    ty: Ty::Bool,
                })
            }
            Expr::String { value: val, .. } => {
                self.emit(Instruction::LoadString {
                    target: Reg::new(reg),
                    val: val.clone(),
                });
                Ok(TypedReg {
                    reg: AnyReg::Str(Reg::new(reg)),
                    ty: Ty::Str,
                })
            }
            Expr::Nil { .. } => {
                unreachable!("nil outside a table release")
            }
            Expr::SysAllocCount { .. } => {
                self.emit(Instruction::SysAllocCount {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            Expr::SysExecCount { .. } => {
                self.emit(Instruction::SysExecCount {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Int(Reg::new(reg)),
                    ty: Ty::Int,
                })
            }
            Expr::FfiModule { .. } => {
                self.emit(Instruction::LoadNull {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::Ffi,
                })
            }
            Expr::CoroModule { .. } => {
                self.emit(Instruction::LoadNull {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::Coro,
                })
            }
            Expr::Function { .. } => {
                self.emit(Instruction::LoadNull {
                    target: Reg::new(reg),
                });
                Ok(TypedReg {
                    reg: AnyReg::Ptr(Reg::new(reg)),
                    ty: Ty::Unknown(0),
                })
            }
            Expr::Call { callee, args, .. } => {
                // the per-instantiation fact key, derived exactly as the
                // checker derives it: the OUTERMOST expansion this call
                // is lowered inside (the call itself at no expansion)
                let call_ptr = expr.id();
                let site = self.expansion_sites.first().copied().unwrap_or(call_ptr);
                // H12/7a, ruling R1 (two-writer shadow): the lowerer's
                // ABSOLUTE loop base must be ONE OF the pair's minted
                // events' break_bases. Membership, not equality: a
                // truth-keyed pair can carry MANY events (a shared body
                // expanded twice in one extent) whose per-event bases
                // legitimately DIVERGE (h12_break_base_is_per_event_pin's
                // program), and the current event's own record is in
                // this set by construction — same walk, same order — so
                // membership never false-fires, while a base matching no
                // minted event is a checker/lowerer desync. Debug-only
                // and graceful so a checker/lowerer site desync still
                // reaches the fact-site guard below, and release bytes
                // are untouched. 7b's ordered cursor reads the event's
                // OWN record and retires this check with the stacks.
                if let Some(&owner) = self.shape.instance_of.get(&(call_ptr, site))
                    && let Some(owner_rec) = self.shape.instances.get(&owner)
                    && let Some(kids) = owner_rec.children.get(&call_ptr)
                {
                    debug_assert!(
                        kids.iter().any(|k| {
                            self.shape
                                .instances
                                .get(k)
                                .is_some_and(|rec| rec.break_base == self.break_ctxs.len())
                        }),
                        "the shadow (7a): the lowerer's break base matches no \
                         minted event — the checker and the lowerer disagree"
                    );
                }
                // D4 precedence, lower half: a Field callee is a module
                // surface call UNLESS the checker resolved it as an
                // expansion (call_defs carries the decision — the lowerer
                // never re-derives precedence)
                if let Expr::Field { .. } = callee.as_ref()
                    && !self.shape.call_defs.contains_key(&(call_ptr, site))
                {
                    return self.lower_ffi_call(expr, args, reg);
                }
                let fn_ptr = self
                    .shape
                    .call_defs
                    .get(&(call_ptr, site))
                    .copied()
                    .ok_or_else(|| {
                        LowerError(Diagnostic::desync(
                            "Lower Error: a call site with no resolved function — \
                             the checker and the lowerer disagree",
                        ))
                    })?;
                // W3a's dispatch, lower half: a call-through reads the
                // closure VALUE's register — the env pointer. An
                // Identifier callee whose binding carries a Closure type
                // dispatches off the binding's own register; a Field
                // callee reads the record cell ONLY when the checker
                // recorded a closure dispatch — a D4 dot-ns expansion
                // call rides the same callee shape and reads nothing.
                let call_env: Option<Reg<Ptr>> = match callee.as_ref() {
                    Expr::Identifier { name: n, .. } => match self.read_var(n) {
                        Ok(local) if matches!(local.ty, Ty::Closure(_)) => Some(ptr_of(local.reg)?),
                        _ => None,
                    },
                    Expr::Field { obj, name, .. }
                        if self.shape.closure_calls.contains(&(call_ptr, site)) =>
                    {
                        let t_any = self.lower_expr(obj, None)?.reg;
                        let t_reg = ptr_of(t_any)?;
                        let k = self.next_reg();
                        self.emit(Instruction::StrKeyConst {
                            target: Reg::new(k),
                            val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
                        });
                        let cell = self.next_reg();
                        self.emit(Instruction::TableGet(<Ptr as CellRepr>::get(
                            Reg::new(cell),
                            t_reg,
                            TableKey::Str(Reg::new(k)),
                        )));
                        Some(Reg::new(cell))
                    }
                    _ => None,
                };
                if self.inline_stack.contains(&fn_ptr) {
                    return Err(LowerError(Diagnostic::desync(
                        "Lower Error: recursive inlining — \
                         the checker and the lowerer disagree",
                    )));
                }
                let def = self.shape.fn_defs.get(&fn_ptr).cloned().ok_or_else(|| {
                    LowerError(Diagnostic::desync(
                        "Lower Error: a call site names a function with no body — \
                         the checker and the lowerer disagree",
                    ))
                })?;
                let call_ret = self
                    .shape
                    .call_rets
                    .get(&(call_ptr, site))
                    .cloned()
                    .ok_or_else(|| {
                        LowerError(Diagnostic::desync(
                            "Lower Error: a call site with no resolved return — \
                             the checker and the lowerer disagree",
                        ))
                    })?;
                let scope_key = self.shape.fn_scope_keys.get(&fn_ptr).copied();
                let body = def.body();

                let mut arg_regs = Vec::with_capacity(args.len());
                for a in args {
                    let tr = self.lower_expr(a, None)?;
                    let layout = self.lookup_layout_for(a)?;
                    arg_regs.push((tr, layout));
                }

                self.inline_stack.push(fn_ptr);
                self.expansion_sites.push(call_ptr);
                self.expansion_break_bases.push(self.break_ctxs.len());
                self.return_ctxs.push(ReturnCtx {
                    kind: ReturnKind::Inline {
                        ty: call_ret.clone(),
                    },
                    exit: None,
                    args: Vec::new(),
                });
                self.in_block(|an| {
                    for (p, (tr, layout)) in def.params.iter().zip(arg_regs) {
                        an.declare_var(p.clone(), tr.reg, tr.ty, layout);
                    }
                    // W3a: the call-through materializes its captures as
                    // ordinary vars off the env (inside this block's
                    // scope — they die with the expansion)
                    if let Some(env) = call_env {
                        an.enter_env_ctx(env, fn_ptr)?;
                    }
                    for s in body {
                        an.lower_stmt(s)?;
                    }
                    match scope_key {
                        Some(key) => an.emit_scope_frees(key),
                        None => Ok(()),
                    }
                })?;
                let result = self.finalize_return_ctx()?.ok_or_else(|| {
                    LowerError(Diagnostic::desync(
                        "Lower Error: an inline call produced no value — \
                         the checker and the lowerer disagree",
                    ))
                })?;
                if let Some(classes) = self.shape.call_tags.get(&expr.id()).cloned() {
                    let exit = self.current_block;
                    let edge_blocks: Vec<BlockId> = self.blocks[exit]
                        .instrs
                        .iter()
                        .find_map(|i| match i {
                            Instruction::Phi(p) => Some(p.arg_blocks().to_vec()),
                            _ => None,
                        })
                        .unwrap_or_default();
                    if edge_blocks.len() < classes.len() {
                        return Err(LowerError(Diagnostic::desync(
                            "Lower Error: a tagged call's return edges went missing — \
                             the analyzer and the lowerer disagree",
                        )));
                    }
                    let mut tag_args: Vec<(BlockId, AnyReg)> = Vec::new();
                    for (i, &b) in edge_blocks.iter().enumerate() {
                        let class = classes.get(i).copied().unwrap_or(false);
                        let r = self.next_reg();
                        let block = &mut self.blocks[b];
                        block.locs.push(self.cur_loc);
                        block.instrs.push(Instruction::LoadBool {
                            target: Reg::new(r),
                            val: class,
                        });
                        tag_args.push((b, AnyReg::Bool(Reg::new(r))));
                    }
                    let tag_reg = self.next_reg();
                    let phi = phi_of(RegKind::Bool, tag_reg, tag_args)?;
                    self.emit(Instruction::Phi(phi));
                    self.call_tag_regs.insert(expr.id(), Reg::new(tag_reg));
                }
                self.inline_stack.pop();
                self.expansion_sites.pop();
                self.expansion_break_bases.pop();
                if call_env.is_some() {
                    self.env_ctxs.pop();
                }
                Ok(TypedReg {
                    reg: result,
                    ty: call_ret,
                })
            }
            Expr::TableCtor { entries, .. } => {
                let elem = self.shape.elem_of(expr);
                let ctor_site = self.shape.sites.get(&expr.id()).copied();

                // W3a, R3: which fields carry closure faces — their
                // stores ride the Ptr lane and the table's own cells go
                // 8-byte (a closure record's non-closure fields must be
                // Int/Flt/Str; the checker's R3 field-kind rule rejects
                // the rest at the ctor — pinned by
                // escape_record_bool_field_rejected and
                // escape_record_table_field_rejected, folded 2026-10-27
                // after the elem join was shown NOT to reject them: a
                // Bool/Any cell aborted at runtime on the mis-sized
                // record, a table cell double-freed)
                let has_closure_fields = entries.iter().any(|(k, _)| match k {
                    CtorKey::Str(n) => ctor_site
                        .is_some_and(|s| self.shape.closure_fields.contains_key(&(s, n.clone()))),
                    _ => false,
                });

                if matches!(elem, crate::shape::Ty::Unknown(_)) {
                    signal!(trace::TRACE_TABLE_NEW_UNDECIDED);
                }

                let mut has_inline_tables = false;
                for (_, e) in entries {
                    if matches!(e, Expr::TableCtor { .. }) {
                        has_inline_tables = true;
                    }
                }

                let is_stored_parent =
                    ctor_site.is_some_and(|s| self.shape.stored_ctor_parents.contains(&s));

                let contains_tables = matches!(elem, crate::shape::Ty::Tbl(_))
                    && (has_inline_tables || is_stored_parent);

                let mut elem_regs = Vec::with_capacity(entries.len());
                for (key, e) in entries {
                    let TypedReg { reg: r, .. } = self.lower_expr(e, None)?;
                    // a closure field's cell rides the Ptr lane raw —
                    // never packed into an Any elem
                    let is_closure_field = match key {
                        CtorKey::Str(n) => ctor_site.is_some_and(|s| {
                            self.shape.closure_fields.contains_key(&(s, n.clone()))
                        }),
                        _ => false,
                    };
                    let r = if matches!(elem, Ty::Any) && !is_closure_field {
                        self.pack_any(r)?
                    } else {
                        r
                    };
                    elem_regs.push(r);
                }

                if let Some(pairs) = self.shape.ctor_ghost_keeps.get(&expr.id()) {
                    for &(ei, g) in pairs {
                        if let Some(&r) = elem_regs.get(ei)
                            && let Ok(ptr) = ptr_of(r)
                        {
                            self.ghost_keeps.insert(g, ptr);
                        }
                    }
                }

                let mode_bit = match self.lookup_layout_for(expr)? {
                    crate::shape::LayoutVerdict::Sparse => 0x01,
                    _ => 0x00,
                };
                let flags = mode_bit | if contains_tables { 0x80 } else { 0x00 };

                let tbl = Reg::<Ptr>::new(reg);
                // W3a: a closure record's cells are 8-byte (Ptr-lane raw
                // stores share the buffer with Int/Flt/Str fields)
                let new_elem = if has_closure_fields {
                    Ty::Str
                } else {
                    elem.clone()
                };
                self.emit(Instruction::TableNew {
                    target: tbl,
                    elem: new_elem,
                    flags,
                });
                if let Some(&site) = self.shape.sites.get(&expr.id()) {
                    self.handles.site_regs.insert(site, (tbl, self.ctrl_depth));
                }
                for ((key, _), v_reg) in entries.iter().zip(elem_regs) {
                    match key {
                        CtorKey::Const(slot) => {
                            let i_reg = self.next_reg();
                            self.emit(Instruction::LoadInt {
                                target: Reg::new(i_reg),
                                val: *slot,
                            });
                            self.table_set(tbl, TableKey::Int(Reg::new(i_reg)), v_reg, &elem)?;
                        }
                        CtorKey::Str(name) => {
                            let k = self.next_reg();
                            self.emit(Instruction::StrKeyConst {
                                target: Reg::new(k),
                                val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
                            });
                            // W3a, R3: the closure face rides the field —
                            // its cell stores the env pointer raw
                            let store_face = match ctor_site
                                .and_then(|s| self.shape.closure_fields.get(&(s, name.clone())))
                            {
                                Some(&ptr) => Ty::Closure(ptr),
                                None => elem.clone(),
                            };
                            self.table_set(tbl, TableKey::Str(Reg::new(k)), v_reg, &store_face)?;
                        }
                        CtorKey::Expr(ke) => {
                            // the checker runs check_index_key on ctor keys —
                            // String keys are legal and lower to StrKey
                            let key = self.lower_index_key(ke)?;
                            self.table_set(tbl, key, v_reg, &elem)?;
                        }
                    }
                }
                Ok(TypedReg {
                    reg: AnyReg::Ptr(tbl),
                    ty: Ty::Tbl(Box::new(elem)),
                })
            }
            Expr::Index { obj, key, .. } => {
                let t_any = self.lower_expr(obj, None)?.reg;
                let key = self.lower_index_key(key)?;
                let target_ty = self.elem_face_of(obj)?;
                let t_reg = ptr_of(t_any)?;
                let out = self.table_get(reg, t_reg, key, &target_ty);
                Ok(TypedReg {
                    reg: out,
                    ty: target_ty,
                })
            }
            Expr::Field { obj, name, .. } => {
                // Non-callee dot access is a record read: identical to
                // t["name"]. Inlined rather than delegated to a synthetic
                // Index expr, whose clone would allocate a fresh operand
                // the checker never walked. Register order: the get
                // target is allocated before the operand (an untargeted
                // field access still burns its entry register).
                let get_reg = if target.is_some() {
                    reg
                } else {
                    self.next_reg()
                };
                let TypedReg { reg: t_any, .. } = self.lower_expr(obj, None)?;
                let k = self.next_reg();
                self.emit(Instruction::StrKeyConst {
                    target: Reg::new(k),
                    val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
                });
                let target_ty = self.elem_face_of(obj)?;
                let t_reg = ptr_of(t_any)?;
                let out = self.table_get(get_reg, t_reg, TableKey::Str(Reg::new(k)), &target_ty);
                Ok(TypedReg {
                    reg: out,
                    ty: target_ty,
                })
            }
            Expr::Identifier { name, .. } => {
                // W3a's creation: a fn name read as a value mints (or
                // joins) this statement's env and answers the env
                // pointer — a closure value's register IS its env.
                let site = self.fact_site(expr.id());
                if let Some(&ptr) = self.shape.creation_envs.get(&(expr.id(), site)) {
                    let reg = self.mint_env(ptr)?;
                    return Ok(TypedReg {
                        reg: AnyReg::Ptr(reg),
                        ty: Ty::Closure(ptr),
                    });
                }
                let local = self.read_var(name)?;
                if target.is_some() && reg != local.reg.id() {
                    let moved = self.emit_move_into(reg, local.reg);
                    Ok(TypedReg {
                        reg: moved,
                        ty: local.ty,
                    })
                } else {
                    Ok(TypedReg {
                        reg: local.reg,
                        ty: local.ty,
                    })
                }
            }
            Expr::BinaryOp {
                op: op @ (BinOp::And | BinOp::Or),
                left,
                right,
                ..
            } => {
                let l_reg = bool_of(self.lower_expr(left, None)?.reg)?;
                self.emit_arm_temp_frees(left);
                let then_block = self.new_block();
                let else_block = self.new_block();
                let join_block = self.new_block();
                self.terminate(Terminator::Branch {
                    cond: l_reg,
                    true_block: then_block,
                    false_block: else_block,
                });
                let and_op = matches!(op, BinOp::And);
                let (value_block, const_block, short_val) = if and_op {
                    (then_block, else_block, false)
                } else {
                    (else_block, then_block, true)
                };

                self.current_block = value_block;
                let v_reg = self.at_depth(|an| an.lower_expr(right, None))?.reg;
                let value_end = self.current_block;
                self.emit_arm_temp_frees(right);
                self.terminate(Terminator::Jump(join_block));

                self.current_block = const_block;
                let c_reg = self.next_reg();
                self.emit(Instruction::LoadBool {
                    target: Reg::new(c_reg),
                    val: short_val,
                });
                let const_end = const_block;
                self.terminate(Terminator::Jump(join_block));

                self.current_block = join_block;
                let (t_end, t_reg, e_end, e_reg) = if and_op {
                    (value_end, v_reg, const_end, AnyReg::Bool(Reg::new(c_reg)))
                } else {
                    (const_end, AnyReg::Bool(Reg::new(c_reg)), value_end, v_reg)
                };
                let phi = phi_of(RegKind::Bool, reg, vec![(t_end, t_reg), (e_end, e_reg)])?;
                self.emit(Instruction::Phi(phi));
                Ok(TypedReg {
                    reg: AnyReg::Bool(Reg::new(reg)),
                    ty: Ty::Bool,
                })
            }
            Expr::BinaryOp {
                op, left, right, ..
            } => {
                let TypedReg {
                    reg: l_any,
                    ty: l_ty,
                } = self.lower_expr(left, None)?;
                let TypedReg {
                    reg: r_any,
                    ty: r_ty,
                } = self.lower_expr(right, None)?;
                match op {
                    BinOp::Add => match num_pair(l_any, r_any)? {
                        NumPair::II(a, b) => self.num3(Instruction::Add, reg, a, b),
                        NumPair::FF(a, b) => self.num3(Instruction::Add, reg, a, b),
                    },
                    BinOp::Sub => match num_pair(l_any, r_any)? {
                        NumPair::II(a, b) => self.num3(Instruction::Sub, reg, a, b),
                        NumPair::FF(a, b) => self.num3(Instruction::Sub, reg, a, b),
                    },
                    BinOp::Mul => match num_pair(l_any, r_any)? {
                        NumPair::II(a, b) => self.num3(Instruction::Mul, reg, a, b),
                        NumPair::FF(a, b) => self.num3(Instruction::Mul, reg, a, b),
                    },
                    BinOp::Div => {
                        let l_reg = self.promote_to_float(l_any, &l_ty)?;
                        let r_reg = self.promote_to_float(r_any, &r_ty)?;
                        self.emit(Instruction::Div {
                            target: Reg::new(reg),
                            left: l_reg,
                            right: r_reg,
                        });
                    }
                    BinOp::IntDiv => {
                        let rhs_const = const_of(right);
                        match num_pair(l_any, r_any)? {
                            NumPair::II(a, b) => {
                                self.num3r(Instruction::IntDiv, reg, a, b, rhs_const)
                            }
                            NumPair::FF(a, b) => {
                                self.num3r(Instruction::IntDiv, reg, a, b, rhs_const)
                            }
                        }
                    }
                    BinOp::Mod => {
                        let rhs_const = const_of(right);
                        match num_pair(l_any, r_any)? {
                            NumPair::II(a, b) => self.num3r(Instruction::Mod, reg, a, b, rhs_const),
                            NumPair::FF(a, b) => self.num3r(Instruction::Mod, reg, a, b, rhs_const),
                        }
                    }
                    BinOp::LessThan => match ord_pair(l_any, r_any)? {
                        OrdPair::II(a, b) => self.cmp3(Instruction::Less, reg, a, b),
                        OrdPair::FF(a, b) => self.cmp3(Instruction::Less, reg, a, b),
                        OrdPair::BB(a, b) => self.cmp3(Instruction::Less, reg, a, b),
                        OrdPair::SS(a, b) => self.cmp3(Instruction::Less, reg, a, b),
                        OrdPair::PP(a, b) => self.cmp3(Instruction::Less, reg, a, b),
                        OrdPair::AA(..) => {
                            return Err(LowerError(Diagnostic::desync(
                                "Lower Error: an ordering comparison on Any boundary cells — \
                                 the checker and the lowerer disagree",
                            )));
                        }
                    },
                    BinOp::GreaterThan => match ord_pair(l_any, r_any)? {
                        OrdPair::II(a, b) => self.cmp3(Instruction::Less, reg, b, a),
                        OrdPair::FF(a, b) => self.cmp3(Instruction::Less, reg, b, a),
                        OrdPair::BB(a, b) => self.cmp3(Instruction::Less, reg, b, a),
                        OrdPair::SS(a, b) => self.cmp3(Instruction::Less, reg, b, a),
                        OrdPair::PP(a, b) => self.cmp3(Instruction::Less, reg, b, a),
                        OrdPair::AA(..) => {
                            return Err(LowerError(Diagnostic::desync(
                                "Lower Error: an ordering comparison on Any boundary cells — \
                                 the checker and the lowerer disagree",
                            )));
                        }
                    },
                    BinOp::LessEq => match ord_pair(l_any, r_any)? {
                        OrdPair::II(a, b) => self.cmp3(Instruction::Leq, reg, a, b),
                        OrdPair::FF(a, b) => self.cmp3(Instruction::Leq, reg, a, b),
                        OrdPair::BB(a, b) => self.cmp3(Instruction::Leq, reg, a, b),
                        OrdPair::SS(a, b) => self.cmp3(Instruction::Leq, reg, a, b),
                        OrdPair::PP(a, b) => self.cmp3(Instruction::Leq, reg, a, b),
                        OrdPair::AA(..) => {
                            return Err(LowerError(Diagnostic::desync(
                                "Lower Error: an ordering comparison on Any boundary cells — \
                                 the checker and the lowerer disagree",
                            )));
                        }
                    },
                    BinOp::GreaterEq => match ord_pair(l_any, r_any)? {
                        OrdPair::II(a, b) => self.cmp3(Instruction::Geq, reg, a, b),
                        OrdPair::FF(a, b) => self.cmp3(Instruction::Geq, reg, a, b),
                        OrdPair::BB(a, b) => self.cmp3(Instruction::Geq, reg, a, b),
                        OrdPair::SS(a, b) => self.cmp3(Instruction::Geq, reg, a, b),
                        OrdPair::PP(a, b) => self.cmp3(Instruction::Geq, reg, a, b),
                        OrdPair::AA(..) => {
                            return Err(LowerError(Diagnostic::desync(
                                "Lower Error: an ordering comparison on Any boundary cells — \
                                 the checker and the lowerer disagree",
                            )));
                        }
                    },
                    BinOp::Equal => match ord_pair(l_any, r_any)? {
                        OrdPair::II(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                        OrdPair::FF(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                        OrdPair::BB(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                        OrdPair::SS(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                        OrdPair::PP(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                        OrdPair::AA(a, b) => self.cmp3(Instruction::Eq, reg, a, b),
                    },
                    BinOp::NotEqual => {
                        let e = self.next_reg();
                        match ord_pair(l_any, r_any)? {
                            OrdPair::II(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                            OrdPair::FF(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                            OrdPair::BB(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                            OrdPair::SS(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                            OrdPair::PP(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                            OrdPair::AA(a, b) => self.cmp3(Instruction::Eq, e, a, b),
                        }
                        self.emit(Instruction::Not {
                            target: Reg::new(reg),
                            source: Reg::new(e),
                        });
                    }
                    BinOp::And | BinOp::Or => unreachable!(),
                }
                let ty = match op {
                    BinOp::LessThan
                    | BinOp::GreaterThan
                    | BinOp::LessEq
                    | BinOp::GreaterEq
                    | BinOp::Equal
                    | BinOp::NotEqual => Ty::Bool,
                    BinOp::Div => Ty::Flt,
                    _ => {
                        if matches!(l_ty, Ty::Flt) || matches!(r_ty, Ty::Flt) {
                            Ty::Flt
                        } else {
                            Ty::Int
                        }
                    }
                };
                Ok(TypedReg {
                    reg: repr_of(&ty).reg(reg),
                    ty,
                })
            }
            Expr::UnaryOp { op, expr, .. } => match op {
                UnOp::Neg => {
                    let TypedReg {
                        reg: x_any,
                        ty: x_ty,
                    } = self.lower_expr(expr, None)?;
                    let out = match num_single(x_any)? {
                        NumSingle::I(x) => {
                            self.neg1(reg, x);
                            AnyReg::Int(Reg::new(reg))
                        }
                        NumSingle::F(x) => {
                            self.neg1(reg, x);
                            AnyReg::Float(Reg::new(reg))
                        }
                    };
                    Ok(TypedReg { reg: out, ty: x_ty })
                }
                UnOp::Not => {
                    let x_reg = bool_of(self.lower_expr(expr, None)?.reg)?;
                    self.emit(Instruction::Not {
                        target: Reg::new(reg),
                        source: x_reg,
                    });
                    Ok(TypedReg {
                        reg: AnyReg::Bool(Reg::new(reg)),
                        ty: Ty::Bool,
                    })
                }
                UnOp::Len => {
                    if let Expr::String { value: s, .. } = expr.as_ref() {
                        self.emit(Instruction::LoadInt {
                            target: Reg::new(reg),
                            val: s.len() as i64,
                        });
                        return Ok(TypedReg {
                            reg: AnyReg::Int(Reg::new(reg)),
                            ty: Ty::Int,
                        });
                    }
                    let TypedReg { reg: v, ty } = self.lower_expr(expr, None)?;
                    match ty {
                        Ty::Str => {
                            let s_reg = str_lane(v)?;
                            self.emit(Instruction::StrLen {
                                target: Reg::new(reg),
                                s: s_reg,
                            });
                            Ok(TypedReg {
                                reg: AnyReg::Int(Reg::new(reg)),
                                ty: Ty::Int,
                            })
                        }
                        Ty::Any => {
                            let a_reg = any_of(v)?;
                            self.emit(Instruction::AnyLen {
                                target: Reg::new(reg),
                                source: a_reg,
                            });
                            Ok(TypedReg {
                                reg: AnyReg::Int(Reg::new(reg)),
                                ty: Ty::Int,
                            })
                        }
                        Ty::Tbl(_) | Ty::Unknown(_) => {
                            let t_reg = ptr_of(v)?;
                            self.emit(Instruction::TableLen {
                                target: Reg::new(reg),
                                table: t_reg,
                            });
                            Ok(TypedReg {
                                reg: AnyReg::Int(Reg::new(reg)),
                                ty: Ty::Int,
                            })
                        }
                        _ => Err(LowerError(Diagnostic::desync(
                            "Lower Error: '#' requires a String, table, or Any operand — \
                             the checker and the lowerer disagree",
                        ))),
                    }
                }
            },
        }
    }
}
