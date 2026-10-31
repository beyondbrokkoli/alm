impl<'a> IrLowerer<'a> {

    /// The per-instantiation half of the access/key fact keys, derived
    /// exactly as the checker derives them (`fact_site` there): the
    /// OUTERMOST expansion the current expression is being lowered
    /// inside — the expression itself at no expansion.
    fn fact_site(&self, expr: NodeId) -> NodeId {
        self.expansion_sites.first().copied().unwrap_or(expr)
    }

    /// Table keys: a String literal folds to its negative interned
    /// identity at COMPILE time (StrKeyConst — the whole point of
    /// hash-derived keys: zero runtime work for `t.x` / `t["x"]` /
    /// record fields); a String-typed dynamic key (`t[s]`) lowers to
    /// alm_str_key (StrKey — one prefix load off the pooled handle);
    /// anything else is the existing Integer lane. The returned
    /// TableKey keeps the two lanes apart at the type level: only the
    /// two derivations can construct the Str lane, so no user integer
    /// can address a record cell. WHICH lane a dynamic key rides is
    /// the checker's recorded decision (`index_key_lanes`, signal 178)
    /// — this walk consumes it, never re-derives it.
    fn lower_index_key(&mut self, key: &Expr) -> Result<TableKey, LowerError> {
        if let Expr::String { value: s, .. } = key {
            let r = self.next_reg();
            self.emit(Instruction::StrKeyConst {
                target: Reg::new(r),
                val: alm_rt::rt::str_key_of_bytes(s.as_bytes()),
            });
            return Ok(TableKey::Str(Reg::new(r)));
        }
        let lane = *self
            .shape
            .index_key_lanes
            .get(&(key.id(), self.fact_site(key.id())))
            .ok_or_else(|| {
                LowerError(Diagnostic::desync(
                    "Lower Error: an index key carries no recorded lane — \
                     the checker and the lowerer disagree",
                ))
            })?;
        let TypedReg { reg, .. } = self.lower_expr(key, None)?;
        match lane {
            KeyLane::Str => {
                // a String read out of a cell (or joined at a phi) carries
                // the pointer face; the two are the same pooled handle
                let s = str_lane(reg)?;
                let r = self.next_reg();
                self.emit(Instruction::StrKey {
                    target: Reg::new(r),
                    s,
                });
                signal!(trace::TRACE_LOWER_KEY_LANE);
                Ok(TableKey::Str(Reg::new(r)))
            }
            KeyLane::Int => {
                signal!(trace::TRACE_LOWER_KEY_LANE);
                Ok(TableKey::Int(int_of(reg)?))
            }
        }
    }

    /// The elem face of one access base, consumed straight from the
    /// checker's recorded decision (signal 180's fact) — the lowerer
    /// never re-derives the elem from its own type walk: one view of
    /// one cell kind everywhere, including adoption-bridged names.
    fn elem_face_of(&self, obj: &Expr) -> Result<Ty, LowerError> {
        let elem = self
            .shape
            .access_elems
            .get(&(obj.id(), self.fact_site(obj.id())))
            .cloned()
            .ok_or_else(|| {
                LowerError(Diagnostic::desync(
                    "Lower Error: a table access carries no recorded elem face — \
                     the checker and the lowerer disagree",
                ))
            })?;
        signal!(trace::TRACE_LOWER_ELEM_FACE);
        Ok(elem)
    }
}
