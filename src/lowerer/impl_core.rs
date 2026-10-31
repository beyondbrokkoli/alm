impl<'a> IrLowerer<'a> {
    pub fn new(shape: &'a ShapeFacts) -> Self {
        Self {
            blocks: vec![BasicBlock::new(0)],
            diagnostics: Vec::new(),
            current_block: 0,
            free_reg: 0,
            scopes: vec![BTreeMap::new()],
            fills: FillCtxs {
                loop_ctxs: Vec::new(),
            },
            shape,
            cur_loc: None,
            handles: FreeHandles {
                site_regs: BTreeMap::new(),
            },
            ghost_keeps: BTreeMap::new(),
            if_tag_regs: BTreeMap::new(),
            call_tag_regs: BTreeMap::new(),
            ctrl_depth: 0,
            return_ctxs: Vec::new(),
            break_ctxs: Vec::new(),
            inline_stack: Vec::new(),
            expansion_sites: Vec::new(),
            expansion_break_bases: Vec::new(),
            env_memo: None,
            env_regs: Vec::new(),
            env_ctxs: Vec::new(),
            cur_stmt: None,
        }
    }

    fn new_block(&mut self) -> BlockId {
        let id = self.blocks.len();
        self.blocks.push(BasicBlock::new(id));
        id
    }

    fn next_reg(&mut self) -> RegId {
        let r = self.free_reg;
        self.free_reg += 1;
        r
    }

    fn emit(&mut self, instr: Instruction) {
        let block = &mut self.blocks[self.current_block];
        block.locs.push(self.cur_loc);
        block.instrs.push(instr);
    }

    fn terminate(&mut self, term: Terminator) {
        let block = &mut self.blocks[self.current_block];
        block.term_loc = self.cur_loc;
        block.terminator = Some(term);
    }

    fn push_dbg_bind(&mut self, name: &str, reg: AnyReg, param: Option<u32>) {
        let after = self.blocks[self.current_block].instrs.len().checked_sub(1);
        if let Some(after) = after {
            self.blocks[self.current_block].dbg_values.push(DbgBind {
                after,
                name: name.to_string(),
                reg: reg.id(),
                kind: reg.kind(),
                loc: self.cur_loc,
                param,
            });
        }
    }

    fn in_block<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.scopes.push(BTreeMap::new());
        self.ctrl_depth += 1;
        let r = f(self);
        self.ctrl_depth -= 1;
        self.scopes.pop();
        r
    }

    fn at_depth<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.ctrl_depth += 1;
        let r = f(self);
        self.ctrl_depth -= 1;
        r
    }

    fn in_do<R>(&mut self, f: impl FnOnce(&mut Self) -> R) -> R {
        self.scopes.push(BTreeMap::new());
        let r = f(self);
        self.scopes.pop();
        r
    }

    fn emit_scope_frees(&mut self, key: (NodeId, u8)) -> Result<(), LowerError> {
        let frees = self
            .shape
            .do_exit_frees
            .get(&key)
            .cloned()
            .unwrap_or_default();
        self.emit_frees(&frees)?;
        if let Some(arms) = self.shape.arm_do_exit_frees.get(&key) {
            for e in arms {
                self.emit_arm_free(e)?;
            }
        }
        Ok(())
    }

    fn resolve_keeps(&self, keeps: &[Keep]) -> Result<Vec<Reg<Ptr>>, LowerError> {
        let mut regs = Vec::new();
        for k in keeps {
            match k {
                Keep::Name(n) => {
                    let local = self.read_var(n)?;
                    let reg = ptr_of(local.reg).map_err(|_| {
                        LowerError(Diagnostic::desync(format!(
                            "Lower Error: borrower '{n}' planned as a keep holds a \
                             non-pointer register — the analyzer and the lowerer disagree"
                        )))
                    })?;
                    regs.push(reg);
                }
                Keep::Ghost(g) => {
                    let &r = self.ghost_keeps.get(g).ok_or_else(|| {
                        LowerError(Diagnostic::desync(
                            "Lower Error: a housed row's keep register was never \
                             captured — the analyzer and the lowerer disagree",
                        ))
                    })?;
                    regs.push(r);
                }
            }
        }
        regs.sort_unstable_by_key(|r| r.id);
        regs.dedup_by_key(|r| r.id);
        Ok(regs)
    }

    fn emit_arm_free(&mut self, e: &ArmFreeEntry) -> Result<(), LowerError> {
        let tag = match e.tag {
            TagSrc::If(stmt) => self.if_tag_regs.get(&stmt).copied(),
            TagSrc::Call(expr) => self.call_tag_regs.get(&expr).copied(),
        }
        .ok_or_else(|| {
            LowerError(Diagnostic::desync(
                "Lower Error: a mixed join's tag phi never lowered — \
                 the analyzer and the lowerer disagree",
            ))
        })?;
        let carrier = self.read_var(&e.carrier)?;
        let table = ptr_of(carrier.reg)?;
        let keep_regs = self.resolve_keeps(&e.keeps)?;
        if keep_regs.iter().any(|k| k.id == table.id) {
            return Ok(());
        }
        let c_reg = self.next_reg();
        self.emit(Instruction::LoadBool {
            target: Reg::new(c_reg),
            val: e.nothing_on,
        });
        let eq_reg = self.next_reg();
        self.cmp3(Instruction::Eq, eq_reg, tag, Reg::new(c_reg));
        let nothing_block = self.new_block();
        let free_block = self.new_block();
        let cont = self.new_block();
        self.terminate(Terminator::Branch {
            cond: Reg::new(eq_reg),
            true_block: nothing_block,
            false_block: free_block,
        });
        self.current_block = free_block;
        signal!(trace::TRACE_JOIN_ARM_FREE);
        if keep_regs.is_empty() {
            self.emit(Instruction::TableFree { table });
        } else {
            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
            self.emit(Instruction::TableFreeExcept {
                table,
                keeps: keep_regs,
            });
        }
        self.terminate(Terminator::Jump(cont));
        self.current_block = nothing_block;
        self.terminate(Terminator::Jump(cont));
        self.current_block = cont;
        Ok(())
    }

    fn emit_frees(&mut self, frees: &[DoExitFree]) -> Result<(), LowerError> {
        let mut plain: Vec<Reg<Ptr>> = Vec::new();
        let mut kept: Vec<(Reg<Ptr>, Vec<Reg<Ptr>>)> = Vec::new();
        for f in frees {
            let carrier = self.read_var(&f.carrier)?;
            // W3a's Extraction Law, lowering half: a closure-typed
            // register is a VIEW of its env — the mint is the one
            // owner, freed at root exit. A closure carrier here means
            // a face read reached a binding past the checker's
            // reject; freeing the view would fire an untracked second
            // free on a live env.
            if matches!(carrier.ty, Ty::Closure(_)) {
                return Err(LowerError(Diagnostic::desync(format!(
                    "a closure value's env has one owner (its mint) — '{}' carries a \
                     face; the checker and the lowerer disagree",
                    f.carrier
                ))));
            }
            let table = ptr_of(carrier.reg)?;
            signal!(trace::TRACE_DO_EXIT_FREE_PHI);
            if f.keeps.is_empty() {
                plain.push(table);
            } else {
                kept.push((table, self.resolve_keeps(&f.keeps)?));
            }
        }

        plain.sort_unstable_by_key(|reg| reg.id);
        plain.dedup_by_key(|reg| reg.id);
        let mut seen: BTreeSet<RegId> = BTreeSet::new();
        for (table, keeps) in kept {
            if keeps.iter().any(|k| k.id == table.id) || !seen.insert(table.id) {
                continue;
            }
            signal!(trace::TRACE_DO_EXIT_KEEP_FREE);
            self.emit(Instruction::TableFreeExcept { table, keeps });
        }
        for reg in plain.into_iter().rev() {
            if !seen.insert(reg.id) {
                continue;
            }
            self.emit(Instruction::TableFree { table: reg });
        }
        Ok(())
    }

    fn emit_root_frees(&mut self) -> Result<(), LowerError> {
        // W3a (the pin-owed register, census §3 cluster B row 17): an
        // env is never one of their keeps — the analyzer's keep
        // computation has no env concept, so nothing structural
        // verifies it; a keep naming an env register would exempt it
        // from the deep free it still needs (a leak). The census fires
        // in debug/test builds at the one site where envs and keeps
        // meet: the root tail, after every mint, before the env frees.
        for f in &self.shape.root_exit_frees {
            for k in &f.keeps {
                if let Keep::Name(n) = k {
                    let local = self.read_var(n)?;
                    let reg = ptr_of(local.reg).map_err(|_| {
                        LowerError(Diagnostic::desync(format!(
                            "Lower Error: borrower '{n}' planned as a keep holds a \
                             non-pointer register — the analyzer and the lowerer disagree"
                        )))
                    })?;
                    debug_assert!(
                        !self.env_regs.iter().any(|e| e.id == reg.id),
                        "an env register rode a root free's keeps — the env's one \
                         owner is its mint"
                    );
                }
            }
        }
        self.emit_frees(&self.shape.root_exit_frees)?;
        let arms = self.shape.arm_root_exit_frees.clone();
        for e in &arms {
            self.emit_arm_free(e)?;
        }
        // W3a, W3-R1: envs live to root exit. The deep free reclaims
        // the whole tree — boxes and moved-in tables alike — after the
        // name-carried frees (an env is never one of their keeps).
        let envs = std::mem::take(&mut self.env_regs);
        for env in envs {
            self.emit(Instruction::TableFree { table: env });
        }
        Ok(())
    }

    fn emit_stmt_temp_frees(&mut self, stmt: &Stmt) {
        let Some(sites) = self.shape.stmt_temp_frees.get(&stmt.id()) else {
            return;
        };
        self.emit_site_frees(sites, trace::TRACE_STMT_TEMP_FREE);
    }

    fn emit_cond_temp_frees(&mut self, stmt: &Stmt) {
        let Some(sites) = self.shape.cond_temp_frees.get(&stmt.id()) else {
            return;
        };
        self.emit_site_frees(sites, trace::TRACE_COND_TEMP_FREE);
    }

    fn emit_arm_temp_frees(&mut self, operand: &Expr) {
        let Some(sites) = self.shape.arm_temp_frees.get(&operand.id()) else {
            return;
        };
        self.emit_site_frees(sites, trace::TRACE_ARM_TEMP_FREE);
    }

    fn emit_site_frees(&mut self, sites: &[usize], slot: u8) {
        let mut free_regs: Vec<Reg<Ptr>> = sites
            .iter()
            .filter_map(|site| self.handles.site_regs.get(site).map(|(reg, _)| *reg))
            .collect();
        free_regs.sort_unstable_by_key(|reg| reg.id);
        free_regs.dedup_by_key(|reg| reg.id);
        for reg in free_regs.into_iter().rev() {
            signal!(slot);
            self.emit(Instruction::TableFree { table: reg });
        }
    }

    // The String repr invariant lives HERE, at the two binding choke
    // points: a value whose static type is String always enters (and
    // therefore leaves) the variable table tagged Str, whatever physical
    // path produced the register (cell reads, phis, nulls all emit the
    // pointer kind). Consumers can rely on it; producers need no
    // per-site normalization.
    fn declare_var(&mut self, name: String, reg: AnyReg, ty: Ty, layout: LayoutVerdict) {
        let reg = string_repr(&ty, reg);
        self.push_dbg_bind(&name, reg, None);
        self.scopes
            .last_mut()
            .unwrap()
            .insert(name, Local { reg, ty, layout });
    }

    fn update_var(
        &mut self,
        name: &str,
        reg: AnyReg,
        ty: Ty,
        layout: LayoutVerdict,
    ) -> Result<(), LowerError> {
        let reg = string_repr(&ty, reg);
        for scope in self.scopes.iter_mut().rev() {
            if let Some(local) = scope.get_mut(name) {
                local.reg = reg;
                local.ty = ty;
                local.layout = layout;
                self.push_dbg_bind(name, reg, None);
                return Ok(());
            }
        }
        Err(LowerError(Diagnostic::lower("Undeclared variable")))
    }

    fn read_var(&self, name: &str) -> Result<Local, LowerError> {
        for scope in self.scopes.iter().rev() {
            if let Some(local) = scope.get(name) {
                return Ok(local.clone());
            }
        }
        Err(LowerError(Diagnostic::lower("Undeclared variable")))
    }

    fn has_var(&self, name: &str) -> bool {
        for scope in self.scopes.iter().rev() {
            if scope.contains_key(name) {
                return true;
            }
        }
        false
    }

    fn holds_value(&self, name: &str) -> bool {
        self.read_var(name)
            .is_ok_and(|local| !matches!(local.ty, Ty::Unknown(_)))
    }

    fn null_moved(&mut self, src: &str) -> Result<(), LowerError> {
        let local = self.read_var(src)?;
        let null_reg = self.next_reg();
        self.emit(Instruction::LoadNull {
            target: Reg::new(null_reg),
        });
        self.update_var(
            src,
            AnyReg::Ptr(Reg::new(null_reg)),
            local.ty.clone(),
            local.layout,
        )
    }

    fn null_moves_of(&mut self, stmt: &Stmt) -> Result<(), LowerError> {
        if let Some(srcs) = self.shape.move_poisons.get(&stmt.id()) {
            for src in srcs.clone() {
                self.null_moved(&src)?;
            }
        }
        Ok(())
    }
}
