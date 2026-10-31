impl<'a> IrLowerer<'a> {

    fn lower_stmt(&mut self, stmt: &Stmt) -> Result<(), LowerError> {
        self.cur_loc = Some(SourceLoc {
            line: stmt.loc().line,
            col: stmt.loc().col,
        });
        // W3a: one env per creation statement (sibling sharing) — the
        // memo resets at every statement lowering
        self.env_memo = None;
        self.cur_stmt = Some(stmt.id());
        match stmt {
            Stmt::LocalDecl { names, exprs, .. } => {
                let mut bindings = Vec::with_capacity(exprs.len());
                for expr in exprs {
                    let target_reg = self.next_reg();
                    let TypedReg { reg, ty } = self.lower_expr(expr, Some(target_reg))?;
                    let layout = self.lookup_layout_for(expr)?;
                    bindings.push((reg, ty, layout));
                }
                while bindings.len() < names.len() {
                    let name = &names[bindings.len()];
                    let ty = self
                        .shape
                        .local_types
                        .get(&(
                            stmt.id(),
                            self.expansion_sites.first().copied(),
                            name.clone(),
                        ))
                        .cloned()
                        .ok_or_else(|| {
                            LowerError(Diagnostic::desync(
                                "Lower Error: a bare declaration carries no resolved type — \
                                 the checker and the lowerer disagree",
                            ))
                        })?;
                    let reg_id = self.next_reg();
                    let reg = match &ty {
                        Ty::Int => {
                            self.emit(Instruction::LoadInt {
                                target: Reg::new(reg_id),
                                val: 0,
                            });
                            AnyReg::Int(Reg::new(reg_id))
                        }
                        Ty::Flt => {
                            self.emit(Instruction::LoadFloat {
                                target: Reg::new(reg_id),
                                val: 0.0,
                            });
                            AnyReg::Float(Reg::new(reg_id))
                        }
                        Ty::Bool => {
                            self.emit(Instruction::LoadBool {
                                target: Reg::new(reg_id),
                                val: false,
                            });
                            AnyReg::Bool(Reg::new(reg_id))
                        }
                        Ty::Tbl(_) | Ty::Unknown(_) | Ty::Str | Ty::Closure(_) => {
                            self.emit(Instruction::LoadNull {
                                target: Reg::new(reg_id),
                            });
                            AnyReg::Ptr(Reg::new(reg_id))
                        }
                        Ty::Ffi | Ty::FfiLib | Ty::Coro => {
                            self.emit(Instruction::LoadNull {
                                target: Reg::new(reg_id),
                            });
                            AnyReg::Ptr(Reg::new(reg_id))
                        }
                        Ty::Any => {
                            self.emit(Instruction::LoadAnyZero {
                                target: Reg::new(reg_id),
                            });
                            AnyReg::Any(Reg::new(reg_id))
                        }
                        // local_types is a resolved constraint-store value —
                        // flow state never rides the artifact path
                        Ty::Pending | Ty::Conflict => {
                            unreachable!("flow state never rides the artifact path")
                        }
                    };
                    bindings.push((reg, ty, LayoutVerdict::default()));
                }
                if let Some(names) = self.shape.rebind_frees.get(&stmt.id()) {
                    for (n, keeps) in names {
                        let displaced = self.read_var(n)?;
                        let table = ptr_of(displaced.reg)?;
                        let keep_regs = self.resolve_keeps(keeps)?;
                        if keep_regs.iter().any(|k| k.id == table.id) {
                            continue;
                        }
                        if keep_regs.is_empty() {
                            self.emit(Instruction::TableFree { table });
                        } else {
                            signal!(trace::TRACE_REBIND_FREE);
                            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
                            self.emit(Instruction::TableFreeExcept {
                                table,
                                keeps: keep_regs,
                            });
                        }
                        signal!(trace::TRACE_REBIND_FREE);
                    }
                }
                if let Some(arms) = self.shape.arm_rebind_frees.get(&stmt.id()) {
                    for e in arms {
                        self.emit_arm_free(e)?;
                    }
                }
                for (name, (reg, ty, layout)) in names.iter().zip(bindings) {
                    self.declare_var(name.clone(), reg, ty, layout);
                }
                self.null_moves_of(stmt)?;
                self.emit_stmt_temp_frees(stmt);
            }
            Stmt::Assignment { name, expr, .. } => {
                // the sugar's #define face (D4): a fn-literal assignment
                // to a name the lowering tables do not hold DECLARES it —
                // the same placeholder slot `local f = function` gets
                // (expansions resolve through the call-site facts, the
                // name slot never carries a value)
                if matches!(expr, Expr::Function { .. }) && !self.has_var(name) {
                    let target_reg = self.next_reg();
                    let TypedReg { reg, ty } = self.lower_expr(expr, Some(target_reg))?;
                    let layout = self.lookup_layout_for(expr)?;
                    self.declare_var(name.clone(), reg, ty, layout);
                    return Ok(());
                }
                if matches!(expr, Expr::Nil { .. }) {
                    let local = self.read_var(name)?;
                    if self.shape.is_free(stmt) {
                        let table = ptr_of(local.reg)?;
                        let keep_regs = self
                            .shape
                            .free_keeps
                            .get(&stmt.id())
                            .map(|ks| self.resolve_keeps(ks))
                            .transpose()?
                            .unwrap_or_default();
                        if keep_regs.iter().any(|k| k.id == table.id) {
                        } else if keep_regs.is_empty() {
                            self.emit(Instruction::TableFree { table });
                        } else {
                            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
                            self.emit(Instruction::TableFreeExcept {
                                table,
                                keeps: keep_regs,
                            });
                        }
                    }
                    if let Some(arms) = self.shape.arm_free_sites.get(&stmt.id()) {
                        for e in arms {
                            self.emit_arm_free(e)?;
                        }
                    }
                    let null_reg = self.next_reg();
                    self.emit(Instruction::LoadNull {
                        target: Reg::new(null_reg),
                    });
                    self.update_var(
                        name,
                        AnyReg::Ptr(Reg::new(null_reg)),
                        local.ty.clone(),
                        local.layout,
                    )?;
                    return Ok(());
                }
                let new_reg = self.next_reg();
                let TypedReg {
                    reg: actual_reg,
                    ty,
                } = self.lower_expr(expr, Some(new_reg))?;
                let layout = self.lookup_layout_for(expr)?;
                if let Some(names) = self.shape.rebind_frees.get(&stmt.id()) {
                    for (n, keeps) in names {
                        let displaced = self.read_var(n)?;
                        let table = ptr_of(displaced.reg)?;
                        let keep_regs = self.resolve_keeps(keeps)?;
                        if keep_regs.iter().any(|k| k.id == table.id) {
                            continue;
                        }
                        if keep_regs.is_empty() {
                            self.emit(Instruction::TableFree { table });
                        } else {
                            signal!(trace::TRACE_REBIND_FREE);
                            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
                            self.emit(Instruction::TableFreeExcept {
                                table,
                                keeps: keep_regs,
                            });
                        }
                        signal!(trace::TRACE_REBIND_FREE);
                    }
                }
                if let Some(arms) = self.shape.arm_rebind_frees.get(&stmt.id()) {
                    for e in arms {
                        self.emit_arm_free(e)?;
                    }
                }
                self.update_var(name, actual_reg, ty, layout)?;
                // W3a: a captured scalar's rebind writes the env box —
                // later calls (and siblings) read it back (L3)
                self.env_write_back(name, actual_reg)?;
                self.null_moves_of(stmt)?;
                self.emit_stmt_temp_frees(stmt);
            }
            Stmt::IndexAssign {
                obj, key, value, ..
            } => {
                let TypedReg { reg: t_any, .. } = self.lower_expr(obj, None)?;
                let t_reg = ptr_of(t_any)?;
                let key = self.lower_index_key(key)?;

                let base_name = get_base_identifier(obj);

                // Fill conversion: the guard rides the Integer lane, so
                // only TableKey::Int can match a fill context — a record
                // store is never fast-pathed.
                let mut fast_guard: Option<Reg<Int>> = None;
                let mut row_reserve: Option<(Reg<Ptr>, Reg<Int>)> = None;
                if let TableKey::Int(g) = key {
                    for ctx in self.fills.loop_ctxs.iter_mut().rev() {
                        if ctx.guard_reg == g.id {
                            if ctx.reserved.contains(&t_reg.id) {
                                fast_guard = Some(g);
                                break;
                            } else if let Some(name) = base_name
                                && let Some((_, bound)) =
                                    ctx.nested_fills.iter().find(|(n, _)| n == name)
                            {
                                ctx.reserved.push(t_reg.id);
                                row_reserve = Some((t_reg, *bound));
                                fast_guard = Some(g);
                                break;
                            }
                        }
                    }
                }
                if let Some((table, bound)) = row_reserve {
                    self.emit(Instruction::TableReserve { table, bound });
                }

                let store_elem = self.elem_face_of(obj)?;
                let v_reg = self.lower_expr(value, None)?.reg;
                let v_reg = if matches!(store_elem, Ty::Any) {
                    self.pack_any(v_reg)?
                } else {
                    v_reg
                };

                if let Some(ghosts) = self.shape.store_ghost_keeps.get(&stmt.id()) {
                    let row_ptr = ptr_of(v_reg)?;
                    for &g in ghosts {
                        self.ghost_keeps.insert(g, row_ptr);
                    }
                }

                if let Some(g) = fast_guard {
                    let layout = self.lookup_layout_for(obj)?;
                    self.table_set_fast(t_reg, g, v_reg, &store_elem, layout)?;
                } else {
                    self.table_set(t_reg, key, v_reg, &store_elem)?;
                }

                if matches!(value, Expr::TableCtor { .. })
                    && let Some(name) = base_name
                {
                    let bound_reg = self.fills.loop_ctxs.iter().rev().find_map(|ctx| {
                        ctx.nested_fills
                            .iter()
                            .find(|(n, _)| n == name)
                            .map(|(_, b_reg)| *b_reg)
                    });

                    if let Some(b_reg) = bound_reg {
                        self.emit(Instruction::TableReserve {
                            table: ptr_of(v_reg)?,
                            bound: b_reg,
                        });
                    }
                }

                self.null_moves_of(stmt)?;
                self.emit_stmt_temp_frees(stmt);
            }
            Stmt::While {
                condition, body, ..
            } => {
                let pre_header = self.current_block;

                let header_block = self.new_block();
                let body_block = self.new_block();
                let exit_block = self.new_block();

                // the loop's phi bases (mutation + moves, the deep
                // facts-fed scan) — the fill-conversion decision no
                // longer rides this set (H9: the walk's recorded plan
                // owns acceptance); the loop's phis still do
                let mut mutated_vars = find_mutated_vars(body, self.shape);
                mutated_vars.extend(find_moved_names(body, self.shape));

                let mut phi_order: Vec<(String, Local)> = mutated_vars
                    .iter()
                    .filter(|name| self.holds_value(name))
                    .map(|name| {
                        let local = self.read_var(name)?;
                        Ok((name.clone(), local))
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?;
                phi_order.sort_by(|(name_a, a), (name_b, b)| {
                    (a.reg.id(), name_a).cmp(&(b.reg.id(), name_b))
                });

                let conv: Option<(String, Vec<String>, BTreeSet<String>)> = match condition {
                    Expr::BinaryOp {
                        op: BinOp::LessThan,
                        left,
                        ..
                    } if as_ident(left).is_some() => {
                        let guard = as_ident(left).expect("guarded by as_ident");
                        // H9: acceptance was decided ONCE by the walk's
                        // predicate (no break, guard born nonneg and only
                        // ascending, stable bound) and recorded as the
                        // loop's FillPlan — consumption filters stay
                        // here: the local must be live, and the base's
                        // dense verdict must match this lowering's depth
                        self.shape
                            .fill_loops
                            .get(&stmt.id())
                            .map(|plan| {
                                let depth = self.scopes.len();
                                let mut names = Vec::new();
                                for name in &plan.fills {
                                    if !self.has_var(name) {
                                        continue;
                                    }
                                    if self.shape.is_dense_at_depth(name, depth) {
                                        names.push(name.clone());
                                    }
                                }
                                (guard.to_string(), names, plan.nested_fills.clone())
                            })
                            .filter(|(_, names, nested)| !names.is_empty() || !nested.is_empty())
                    }
                    _ => None,
                };
                let conv_bound: Option<&Expr> = match condition {
                    Expr::BinaryOp {
                        op: BinOp::LessThan,
                        right: bound_expr,
                        ..
                    } if conv.is_some() => Some(bound_expr),
                    _ => None,
                };
                let mut conv_bound_reg: Option<Reg<Int>> = None;
                if let (Some((_, names, _)), Some(bound_expr)) = (&conv, conv_bound) {
                    let saved_scopes = self.scopes.clone();
                    let TypedReg { reg: b_any, .. } = self.lower_expr(bound_expr, None)?;
                    self.scopes = saved_scopes;
                    let b_reg = int_of(b_any)?;
                    conv_bound_reg = Some(b_reg);
                    for name in names {
                        let t_reg = ptr_of(self.read_var(name)?.reg)?;
                        self.emit(Instruction::TableReserve {
                            table: t_reg,
                            bound: b_reg,
                        });
                    }
                    self.emit_cond_temp_frees(stmt);
                }

                let mut phis: Vec<(String, RegId, LayoutVerdict)> = Vec::new();

                self.terminate(Terminator::Jump(header_block));
                self.current_block = header_block;

                for (var, pre_loop_local) in phi_order {
                    let phi_reg = self.next_reg();
                    let phi = phi_of(
                        repr_of(&pre_loop_local.ty),
                        phi_reg,
                        vec![(pre_header, pre_loop_local.reg)],
                    )?;
                    self.emit(Instruction::Phi(phi));
                    self.update_var(
                        &var,
                        repr_of(&pre_loop_local.ty).reg(phi_reg),
                        pre_loop_local.ty.clone(),
                        pre_loop_local.layout,
                    )?;
                    phis.push((var, phi_reg, pre_loop_local.layout));
                }

                let cond_reg = if let (Some((guard, _, _)), Some(b_reg)) = (&conv, conv_bound_reg) {
                    let g_reg = int_of(self.read_var(guard)?.reg)?;
                    let c_reg = self.next_reg();
                    self.cmp3(Instruction::Less, c_reg, g_reg, b_reg);
                    Reg::new(c_reg)
                } else {
                    let r = bool_of(self.lower_expr(condition, None)?.reg)?;
                    self.emit_cond_temp_frees(stmt);
                    r
                };
                self.terminate(Terminator::Branch {
                    cond: cond_reg,
                    true_block: body_block,
                    false_block: exit_block,
                });

                if let Some((guard, names, nested_fills)) = &conv {
                    let guard_reg = self.read_var(guard)?.reg.id();
                    let reserved = names
                        .iter()
                        .map(|name| Ok(self.read_var(name)?.reg.id()))
                        .collect::<Result<Vec<_>, LowerError>>()?;

                    let mut nested_fill_regs: Vec<(String, Reg<Int>)> = Vec::new();
                    for name in names {
                        let local = self.read_var(name)?;
                        if let Ty::Tbl(inner_ty) = &local.ty
                            && matches!(**inner_ty, Ty::Tbl(_))
                        {
                            self.emit(Instruction::TableReserve {
                                table: ptr_of(local.reg)?,
                                bound: conv_bound_reg.unwrap(),
                            });
                            nested_fill_regs.push((name.clone(), conv_bound_reg.unwrap()));
                        }
                    }
                    for name in nested_fills {
                        if self.has_var(name) {
                            let local = self.read_var(name)?;
                            if let Ty::Tbl(inner_ty) = &local.ty
                                && matches!(**inner_ty, Ty::Tbl(_))
                            {
                                self.emit(Instruction::TableReserve {
                                    table: ptr_of(local.reg)?,
                                    bound: conv_bound_reg.unwrap(),
                                });
                                nested_fill_regs.push((name.clone(), conv_bound_reg.unwrap()));
                            }
                        }
                    }

                    self.fills.loop_ctxs.push(LoopCtx {
                        guard_reg,
                        reserved,
                        nested_fills: nested_fill_regs,
                    });
                }

                self.break_ctxs.push(BreakCtx {
                    exit_block,
                    phi_vars: phis.iter().map(|(v, _, _)| v.clone()).collect(),
                    breaks: Vec::new(),
                });
                self.current_block = body_block;
                self.in_block(|an| {
                    for s in body {
                        an.lower_stmt(s)?;
                    }
                    an.emit_scope_frees((stmt.id(), 0))
                })?;
                if conv.is_some() {
                    self.fills.loop_ctxs.pop();
                }
                let break_ctx = self
                    .break_ctxs
                    .pop()
                    .expect("while lowered its body with the BreakCtx pushed");

                let end_of_body = self.current_block;
                self.terminate(Terminator::Jump(header_block));

                for (var, phi_reg, _) in &phis {
                    let back_edge_local = self.read_var(var)?;
                    for instr in &mut self.blocks[header_block].instrs {
                        if let Instruction::Phi(phi) = instr
                            && phi.target_id() == *phi_reg
                        {
                            phi_push(phi, end_of_body, back_edge_local.reg)?;
                            break;
                        }
                    }
                }

                for (var, phi_reg, pre_layout) in &phis {
                    let local = self.read_var(var)?;
                    let layout = pre_layout.join(local.layout);
                    let repr = repr_of(&local.ty);
                    self.update_var(var, repr.reg(*phi_reg), local.ty.clone(), layout)?;
                }

                self.current_block = exit_block;

                if !break_ctx.breaks.is_empty() {
                    for (i, (var, phi_reg, pre_layout)) in phis.iter().enumerate() {
                        let local = self.read_var(var)?;
                        let repr = repr_of(&local.ty);
                        let mut args = Vec::with_capacity(1 + break_ctx.breaks.len());
                        args.push((header_block, repr.reg(*phi_reg)));
                        let mut layout = pre_layout.join(local.layout);
                        for (brk_block, snap) in &break_ctx.breaks {
                            args.push((*brk_block, snap[i].reg));
                            layout = layout.join(snap[i].layout);
                        }
                        let exit_phi = self.next_reg();
                        let phi = phi_of(repr, exit_phi, args)?;
                        self.emit(Instruction::Phi(phi));
                        self.update_var(var, repr.reg(exit_phi), local.ty.clone(), layout)?;
                    }
                }
            }
            Stmt::Do { body, .. } => self.in_do(|an| -> Result<(), LowerError> {
                for s in body {
                    an.lower_stmt(s)?;
                }
                an.emit_scope_frees((stmt.id(), 0))
            })?,

            Stmt::Print { exprs, .. } => {
                let mut operands = Vec::new();
                for e in exprs {
                    let TypedReg { reg: r, ty } = self.lower_expr(e, None)?;
                    operands.push((r.id(), ty));
                }
                self.emit(Instruction::Print { operands });
                self.emit_stmt_temp_frees(stmt);
            }
            Stmt::Expr { expr, .. } => {
                self.lower_expr(expr, None)?;
                self.emit_stmt_temp_frees(stmt);
            }
            Stmt::Break { .. } => {
                // defense in depth: a break inside an expansion may only
                // bind a loop of its OWN body — the innermost ctx below
                // the expansion's base belongs to the caller and must
                // never catch an expansion's break
                if let Some(&base) = self.expansion_break_bases.last()
                    && self.break_ctxs.len() <= base
                {
                    return Err(LowerError(Diagnostic::desync(
                        "Lower Error: 'break' crossing an expansion boundary — \
                         the checker and the lowerer disagree",
                    )));
                }
                let phi_vars = self
                    .break_ctxs
                    .last()
                    .ok_or_else(|| {
                        LowerError(Diagnostic::desync(
                            "Lower Error: 'break' outside of loop — \
                             the checker and the lowerer disagree",
                        ))
                    })?
                    .phi_vars
                    .clone();
                let mut snap = Vec::with_capacity(phi_vars.len());
                for var in &phi_vars {
                    snap.push(self.read_var(var)?);
                }
                let frees = self
                    .shape
                    .break_path_frees
                    .get(&stmt.id())
                    .cloned()
                    .unwrap_or_default();
                self.emit_frees(&frees)?;
                self.emit_stmt_temp_frees(stmt);
                let ctx = self.break_ctxs.last_mut().expect("checked above");
                let exit_block = ctx.exit_block;
                ctx.breaks.push((self.current_block, snap));
                self.terminate(Terminator::Jump(exit_block));
                self.current_block = self.new_block();
            }
            Stmt::Return { value, .. } => {
                let boundary = matches!(
                    self.return_ctxs.last().map(|ctx| &ctx.kind),
                    Some(ReturnKind::Boundary)
                );
                let val_reg = if boundary {
                    match value {
                        None | Some(Expr::Nil { .. }) => {
                            let r = self.next_reg();
                            self.emit(Instruction::LoadNull {
                                target: Reg::new(r),
                            });
                            AnyReg::Ptr(Reg::new(r))
                        }
                        Some(expr) => {
                            let TypedReg { reg, .. } = self.lower_expr(expr, None)?;
                            AnyReg::Ptr(ptr_of(reg)?)
                        }
                    }
                } else {
                    match value {
                        Some(expr) if !matches!(expr, Expr::Nil { .. }) => {
                            self.lower_expr(expr, None)?.reg
                        }
                        _ => {
                            return Err(LowerError(Diagnostic::desync(
                                "Lower Error: an internal 'return' carries a value — \
                                 the checker and the lowerer disagree",
                            )));
                        }
                    }
                };
                let exit = match self.return_ctxs.last_mut().unwrap().exit {
                    Some(exit) => exit,
                    None => {
                        let exit = self.new_block();
                        self.return_ctxs.last_mut().unwrap().exit = Some(exit);
                        exit
                    }
                };
                self.return_ctxs
                    .last_mut()
                    .unwrap()
                    .args
                    .push((self.current_block, val_reg));
                let keep_frees = self
                    .shape
                    .ret_path_keep_frees
                    .get(&stmt.id())
                    .cloned()
                    .unwrap_or_default();
                let keep_temps = self
                    .shape
                    .ret_path_keep_temps
                    .get(&stmt.id())
                    .cloned()
                    .unwrap_or_default();
                if (!keep_frees.is_empty() || !keep_temps.is_empty())
                    && let Ok(keep) = ptr_of(val_reg)
                {
                    for f in &keep_frees {
                        let carrier = self.read_var(&f.carrier)?;
                        let table = ptr_of(carrier.reg)?;
                        if table.id == keep.id {
                            continue;
                        }
                        let mut keeps = vec![keep];
                        keeps.extend(self.resolve_keeps(&f.keeps)?);
                        keeps.sort_unstable_by_key(|k| k.id);
                        keeps.dedup_by_key(|k| k.id);
                        if keeps.iter().any(|k| k.id == table.id) {
                            continue;
                        }
                        signal!(trace::TRACE_RET_KEEP_FREE);
                        if keeps.len() > 1 {
                            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
                        }
                        self.emit(Instruction::TableFreeExcept { table, keeps });
                    }
                    let mut regs: Vec<Reg<Ptr>> = keep_temps
                        .iter()
                        .filter_map(|site| self.handles.site_regs.get(site).map(|(reg, _)| *reg))
                        .collect();
                    regs.sort_unstable_by_key(|reg| reg.id);
                    regs.dedup_by_key(|reg| reg.id);
                    for reg in regs.into_iter().rev() {
                        signal!(trace::TRACE_RET_KEEP_FREE);
                        self.emit(Instruction::TableFreeExcept {
                            table: reg,
                            keeps: vec![keep],
                        });
                    }
                }
                let frees = self
                    .shape
                    .ret_path_frees
                    .get(&stmt.id())
                    .cloned()
                    .unwrap_or_default();
                if !frees.is_empty() {
                    signal!(trace::TRACE_RET_PATH_FREE);
                }
                self.emit_frees(&frees)?;
                self.emit_stmt_temp_frees(stmt);
                // W3a: the creation sever's poison (a ctor return that
                // moved captures into the env zeroes the sources here)
                self.null_moves_of(stmt)?;
                self.terminate(Terminator::Jump(exit));
                self.current_block = self.new_block();
            }
            Stmt::If {
                condition,
                then_body,
                else_body,
                ..
            } => {
                let cond_reg = bool_of(self.lower_expr(condition, None)?.reg)?;
                self.emit_cond_temp_frees(stmt);

                let then_block = self.new_block();
                let else_block = self.new_block();
                let join_block = self.new_block();

                self.terminate(Terminator::Branch {
                    cond: cond_reg,
                    true_block: then_block,
                    false_block: else_block,
                });

                let mut mutated = find_mutated_vars(then_body, self.shape);
                mutated.extend(find_mutated_vars(else_body, self.shape));
                mutated.extend(find_moved_names(then_body, self.shape));
                mutated.extend(find_moved_names(else_body, self.shape));
                let mutated: Vec<String> = mutated
                    .into_iter()
                    .filter(|name| self.holds_value(name))
                    .collect();

                let mut phi_order: Vec<(String, RegId)> = mutated
                    .into_iter()
                    .map(|name| {
                        let local = self.read_var(&name)?;
                        Ok((name, local.reg.id()))
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?;
                phi_order.sort_by(|(name_a, a), (name_b, b)| (a, name_a).cmp(&(b, name_b)));

                let snapshot = self.scopes.clone();

                self.current_block = then_block;
                self.in_block(|an| {
                    for s in then_body {
                        an.lower_stmt(s)?;
                    }
                    an.emit_scope_frees((stmt.id(), 0))
                })?;
                let then_end = self.current_block;
                let then_regs: Vec<(String, AnyReg, Ty, LayoutVerdict)> = phi_order
                    .iter()
                    .map(|(name, _)| {
                        let local = self.read_var(name)?;
                        Ok((name.clone(), local.reg, local.ty, local.layout))
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?;
                let mut then_tag: Option<Reg<Bool>> = None;
                if self.shape.join_tags.contains_key(&stmt.id()) {
                    let r = self.next_reg();
                    self.emit(Instruction::LoadBool {
                        target: Reg::new(r),
                        val: true,
                    });
                    then_tag = Some(Reg::new(r));
                }
                self.terminate(Terminator::Jump(join_block));

                self.scopes = snapshot;
                self.current_block = else_block;
                self.in_block(|an| {
                    for s in else_body {
                        an.lower_stmt(s)?;
                    }
                    an.emit_scope_frees((stmt.id(), 1))
                })?;
                let else_end = self.current_block;
                let else_regs: Vec<(String, AnyReg, Ty, LayoutVerdict)> = phi_order
                    .iter()
                    .map(|(name, _)| {
                        let local = self.read_var(name)?;
                        Ok((name.clone(), local.reg, local.ty, local.layout))
                    })
                    .collect::<Result<Vec<_>, LowerError>>()?;
                let mut else_tag: Option<Reg<Bool>> = None;
                if self.shape.join_tags.contains_key(&stmt.id()) {
                    let r = self.next_reg();
                    self.emit(Instruction::LoadBool {
                        target: Reg::new(r),
                        val: false,
                    });
                    else_tag = Some(Reg::new(r));
                }
                self.terminate(Terminator::Jump(join_block));

                self.current_block = join_block;
                if let (Some(t), Some(e)) = (then_tag, else_tag) {
                    let tag_reg = self.next_reg();
                    let phi = phi_of(
                        RegKind::Bool,
                        tag_reg,
                        vec![(then_end, AnyReg::Bool(t)), (else_end, AnyReg::Bool(e))],
                    )?;
                    self.emit(Instruction::Phi(phi));
                    self.if_tag_regs.insert(stmt.id(), Reg::new(tag_reg));
                }
                for (i, (name, _)) in phi_order.iter().enumerate() {
                    let phi_reg = self.next_reg();
                    let ty = join_phi_ty(&then_regs[i].2, &else_regs[i].2);
                    let joined = repr_of(&ty);
                    let layout = then_regs[i].3.join(else_regs[i].3);
                    let phi = phi_of(
                        joined,
                        phi_reg,
                        vec![(then_end, then_regs[i].1), (else_end, else_regs[i].1)],
                    )?;
                    self.emit(Instruction::Phi(phi));
                    self.update_var(name, joined.reg(phi_reg), ty, layout)?;
                }
            }
        }
        Ok(())
    }
}
