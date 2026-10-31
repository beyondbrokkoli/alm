impl<'a> IrLowerer<'a> {

    /// W3a's ENV MINT (the Env Law, lower half): one env per creation
    /// statement — every cell a table pointer (captured tables direct,
    /// captured scalars in one-cell boxes of their own elem), so the
    /// root-exit deep free is sound on the whole tree at once. Tables
    /// MOVE in (the sources poison through the walk-booked
    /// move_poisons — the existing move law); scalars copy at mint.
    fn mint_env(&mut self, ptr: NodeId) -> Result<Reg<Ptr>, LowerError> {
        let faces: BTreeMap<String, Ty> =
            self.shape.env_faces.get(&ptr).cloned().unwrap_or_default();
        let stmt = self
            .cur_stmt
            .ok_or_else(|| LowerError(Diagnostic::lower("an env mint outside a statement")))?;
        if let Some(memo) = self.take_env_memo_for(stmt) {
            let reg = memo.reg;
            let stored = memo.stored;
            self.store_env_cells(reg, faces, stored)?;
            return Ok(reg);
        }
        let env_id = self.next_reg();
        let env = Reg::new(env_id);
        let flags = 0x01 | if faces.is_empty() { 0x00 } else { 0x80 };
        self.emit(Instruction::TableNew {
            target: env,
            elem: Ty::Str,
            flags,
        });
        self.env_regs.push(env);
        let mut stored = BTreeSet::new();
        for name in faces.keys() {
            stored.insert(name.clone());
        }
        self.store_env_cells(env, faces, BTreeSet::new())?;
        self.env_memo = Some(EnvMemo {
            stmt,
            reg: env,
            stored,
        });
        Ok(env)
    }

    fn take_env_memo_for(&mut self, stmt: NodeId) -> Option<EnvMemo> {
        if let Some(memo) = &self.env_memo
            && memo.stmt == stmt
        {
            return self.env_memo.take();
        }
        None
    }

    fn store_env_cells(
        &mut self,
        env: Reg<Ptr>,
        faces: BTreeMap<String, Ty>,
        already: BTreeSet<String>,
    ) -> Result<(), LowerError> {
        for (name, ty) in faces {
            if already.contains(&name) {
                continue;
            }
            let local = self.read_var(&name)?;
            let key = self.next_reg();
            self.emit(Instruction::StrKeyConst {
                target: Reg::new(key),
                val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
            });
            if matches!(ty, Ty::Tbl(_)) {
                let reg = ptr_of(local.reg)?;
                self.table_set(
                    env,
                    TableKey::Str(Reg::new(key)),
                    AnyReg::Ptr(reg),
                    &Ty::Str,
                )?;
            } else {
                // the scalar's box: one dense cell of its own elem
                let box_id = self.next_reg();
                let box_reg = Reg::new(box_id);
                self.emit(Instruction::TableNew {
                    target: box_reg,
                    elem: ty.clone(),
                    flags: 0,
                });
                let idx = self.next_reg();
                self.emit(Instruction::LoadInt {
                    target: Reg::new(idx),
                    val: 0,
                });
                self.table_set(box_reg, TableKey::Int(Reg::new(idx)), local.reg, &ty)?;
                self.table_set(
                    env,
                    TableKey::Str(Reg::new(key)),
                    AnyReg::Ptr(box_reg),
                    &Ty::Str,
                )?;
            }
            if let Some(memo) = &mut self.env_memo {
                memo.stored.insert(name);
            }
        }
        Ok(())
    }

    /// W3a's call-through env entry: materialize every captured name as
    /// an ordinary var (tables direct, scalars unboxed from their
    /// cells) so the body's own lowering needs no further plumbing;
    /// scalar rebinds write the box back (the Assignment arm consults
    /// `env_ctxs`).
    fn enter_env_ctx(&mut self, env: Reg<Ptr>, ptr: NodeId) -> Result<(), LowerError> {
        let faces: BTreeMap<String, Ty> =
            self.shape.env_faces.get(&ptr).cloned().unwrap_or_default();
        for (name, ty) in faces.clone() {
            let key = self.next_reg();
            self.emit(Instruction::StrKeyConst {
                target: Reg::new(key),
                val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
            });
            let cell_id = self.next_reg();
            let cell = Reg::new(cell_id);
            self.emit(Instruction::TableGet(<Ptr as CellRepr>::get(
                cell,
                env,
                TableKey::Str(Reg::new(key)),
            )));
            if matches!(ty, Ty::Tbl(_)) {
                self.declare_var(name, AnyReg::Ptr(cell), ty, LayoutVerdict::Sparse);
            } else {
                let idx = self.next_reg();
                self.emit(Instruction::LoadInt {
                    target: Reg::new(idx),
                    val: 0,
                });
                let out = self.next_reg();
                let v = self.table_get(out, cell, TableKey::Int(Reg::new(idx)), &ty);
                self.declare_var(name, v, ty, LayoutVerdict::default());
            }
        }
        self.env_ctxs.push(EnvCtx { reg: env, faces });
        Ok(())
    }

    /// The scalar write-back: a captured name's rebind lands in the env
    /// box (later calls — and siblings — read it back; L3).
    fn env_write_back(&mut self, name: &str, value: AnyReg) -> Result<(), LowerError> {
        let Some(ctx) = self.env_ctxs.last().cloned() else {
            return Ok(());
        };
        let Some(ty) = ctx.faces.get(name).cloned() else {
            return Ok(());
        };
        if matches!(ty, Ty::Tbl(_)) {
            return Ok(());
        }
        let key = self.next_reg();
        self.emit(Instruction::StrKeyConst {
            target: Reg::new(key),
            val: alm_rt::rt::str_key_of_bytes(name.as_bytes()),
        });
        let cell_id = self.next_reg();
        let cell = Reg::new(cell_id);
        self.emit(Instruction::TableGet(<Ptr as CellRepr>::get(
            cell,
            ctx.reg,
            TableKey::Str(Reg::new(key)),
        )));
        let idx = self.next_reg();
        self.emit(Instruction::LoadInt {
            target: Reg::new(idx),
            val: 0,
        });
        self.table_set(cell, TableKey::Int(Reg::new(idx)), value, &ty)?;
        Ok(())
    }
}
