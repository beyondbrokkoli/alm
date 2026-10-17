use super::*;
impl Recorded {
    pub(super) fn report_conflict(&mut self, id: usize) -> crate::ast::StaticType {
        if self.ledger.conflict_reported.insert(id) {
            let line = self.ctor_lines[id];
            self.ledger.diagnostics.push(format!(
                "line {line}: Type Error: a table's cells hold one scalar kind — mixing scalar \
                 kinds chooses the dynamic cell (Any), but a table value never rides a cell \
                 (table site #{id})"
            ));
        }
        crate::ast::StaticType::Unknown(id)
    }

    pub(super) fn elem_type_of_tbl(&mut self, id: usize) -> crate::ast::StaticType {
        if self.lattice.site_elem[id] == Conflict {
            signal!(self.recording, trace::TRACE_SHAPE_CONFLICT_GUARD);
            return self.report_conflict(id);
        }

        if let Some(children) = self.lattice.child_sites.get(&id).cloned() {
            signal!(self.recording, trace::TRACE_CHILD_FAST_PATH);
            let mut uniform_type: Option<crate::ast::StaticType> = None;

            for &child_id in &children {
                if self.lattice.site_elem[child_id] == Conflict {
                    signal!(self.recording, trace::TRACE_ELEM_CHILD_CONFLICT);
                    return self.report_conflict(child_id);
                }

                let child_ty = self.elem_type_of_tbl(child_id);

                let child_pending = matches!(child_ty, crate::ast::StaticType::Unknown(_));
                match &uniform_type {
                    None => {
                        signal!(self.recording, trace::TRACE_ELEM_CHILD_FIRST);
                        uniform_type = Some(child_ty.clone());
                    }
                    Some(expected) => {
                        let expected_pending =
                            matches!(expected, crate::ast::StaticType::Unknown(_));
                        if !child_pending && !expected_pending && *expected != child_ty {
                            signal!(self.recording, trace::TRACE_ELEM_CHILD_MISMATCH);
                            return self.report_conflict(child_id);
                        }
                        if expected_pending && !child_pending {
                            uniform_type = Some(child_ty.clone());
                        }
                        signal!(self.recording, trace::TRACE_ELEM_CHILD_MATCH);
                    }
                }
            }

            if let Some(ty) = uniform_type {
                signal!(self.recording, trace::TRACE_ELEM_CHILD_UNIFORM);
                return crate::ast::StaticType::Table(Box::new(ty));
            }
        }

        signal!(self.recording, trace::TRACE_FALLBACK_RESOLVE);
        match self.lattice.site_elem[id].clone() {
            Tbl(inner) => {
                signal!(self.recording, trace::TRACE_ELEM_FALLBACK_TBL);
                crate::ast::StaticType::Table(Box::new(self.ty_to_static(&inner, id)))
            }
            Int => {
                signal!(self.recording, trace::TRACE_ELEM_FALLBACK_INT);
                crate::ast::StaticType::Integer
            }
            Pending => {
                signal!(self.recording, trace::TRACE_ANALYZE_PENDING);
                crate::ast::StaticType::Unknown(id)
            }
            Flt => {
                signal!(self.recording, trace::TRACE_ELEM_FALLBACK_FLT);
                crate::ast::StaticType::Float
            }
            Bool => {
                signal!(self.recording, trace::TRACE_ELEM_FALLBACK_BOOL);
                crate::ast::StaticType::Boolean
            }
            Str => {
                signal!(self.recording, trace::TRACE_ELEM_FALLBACK_STR);
                crate::ast::StaticType::String
            }
            Any => crate::ast::StaticType::Any,
            Ffi => crate::ast::StaticType::Ffi,
            FfiLib => crate::ast::StaticType::FfiLib,
            Coro => crate::ast::StaticType::Coro,
            Conflict => {
                signal!(self.recording, trace::TRACE_ELEM_FALLBACK_CONFLICT);
                self.report_conflict(id)
            }
        }
    }

    pub(super) fn ty_to_static(&mut self, ty: &Ty, site: usize) -> crate::ast::StaticType {
        match ty {
            Int => {
                signal!(self.recording, trace::TRACE_TY_STATIC_INT);
                crate::ast::StaticType::Integer
            }
            Pending => {
                signal!(self.recording, trace::TRACE_TY_STATIC_PENDING);
                let ghost = self.lattice.ghost_next;
                self.lattice.ghost_next -= 1;
                crate::ast::StaticType::Unknown(ghost)
            }
            Flt => {
                signal!(self.recording, trace::TRACE_TY_STATIC_FLT);
                crate::ast::StaticType::Float
            }
            Bool => {
                signal!(self.recording, trace::TRACE_TY_STATIC_BOOL);
                crate::ast::StaticType::Boolean
            }
            Str => {
                signal!(self.recording, trace::TRACE_TY_STATIC_STR);
                crate::ast::StaticType::String
            }
            Any => crate::ast::StaticType::Any,
            Ffi => crate::ast::StaticType::Ffi,
            FfiLib => crate::ast::StaticType::FfiLib,
            Coro => crate::ast::StaticType::Coro,
            Tbl(inner) => {
                signal!(self.recording, trace::TRACE_TY_STATIC_TBL);
                crate::ast::StaticType::Table(Box::new(self.ty_to_static(inner, site)))
            }
            Conflict => {
                signal!(self.recording, trace::TRACE_TY_STATIC_CONFLICT);
                self.report_conflict(site)
            }
        }
    }
}

pub(super) fn propagate_elem_down(
    elems: &mut [crate::ast::StaticType],
    child_sites: &BTreeMap<usize, BTreeSet<usize>>,
    site: usize,
) {
    let crate::ast::StaticType::Table(elem) = elems[site].clone() else {
        return;
    };
    if matches!(*elem, crate::ast::StaticType::Unknown(_)) {
        return;
    }
    if let Some(children) = child_sites.get(&site) {
        for &child in children {
            if matches!(elems[child], crate::ast::StaticType::Unknown(_)) {
                elems[child] = (*elem).clone();
                propagate_elem_down(elems, child_sites, child);
            }
        }
    }
}

impl Analyzer {
    pub(super) fn decide(&mut self, rec: Gate, site: usize, vt: &Ty) {
        signal!(rec.on(), trace::TRACE_DECIDE_VISIT);
        if self.lattice.site_elem[site] == Conflict {
            signal!(rec.on(), trace::TRACE_DECIDE_CONFLICT);
            return;
        }

        let joined = join_ty(&self.lattice.site_elem[site], vt);
        if self.lattice.site_elem[site] != joined {
            self.probe(rec, trace::TRACE_JOIN_RETYPED);
            self.lattice.site_elem[site] = joined.clone();
            self.walk.changed = true;
        }

        let expected_var_ty = Tbl(Box::new(self.lattice.site_elem[site].clone()));

        let Self {
            walk:
                WalkState {
                    scopes,
                    conv_fires,
                    changed,
                    ..
                },
            ..
        } = self;
        for scope in scopes.iter_mut() {
            for ts in scope.values_mut() {
                if ts.aliases.contains(&site)
                    && !is_root(&site)
                    && (ts.ty == Pending || ts.ty != expected_var_ty)
                {
                    if rec.on() {
                        trace::compiler_trace_signal(trace::TRACE_DECIDE_UPDATE);
                    } else {
                        conv_fires.insert(trace::TRACE_DECIDE_UPDATE);
                    }
                    ts.ty = expected_var_ty.clone();
                    if ts.ty != Pending {
                        if rec.on() {
                            trace::compiler_trace_signal(trace::TRACE_DECIDE_UPDATE_CHANGED);
                        } else {
                            conv_fires.insert(trace::TRACE_DECIDE_UPDATE_CHANGED);
                        }
                        *changed = true;
                    }
                }
            }
        }
    }
}
