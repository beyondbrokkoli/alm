use super::*;
// elem_type_of_tbl lives on Analyzer (not Recorded): the static-elem
// table is computed BEFORE the recorded pass so the checker checks
// against the exact table the assembled facts carry. These are not
// language conversions but the elem table's MATERIALIZATION policy over
// the one type language — a top-level Pending site rides as
// `Unknown(site)` (its pins close in the constraint store), a NESTED
// Pending rides as a fresh ghost `Unknown` (the MAX/2-down ghost
// discipline), Conflict reports.
// Downstream of the table only decided kinds and Unknowns exist — the
// invariant the artifact path's `unreachable!` arms rest on.
impl Analyzer {
    pub(super) fn report_conflict(&mut self, id: usize) -> Ty {
        if self.ledger.conflict_reported.insert(id) {
            let line = self.ctor_lines[id];
            self.ledger.diagnostics.push(format!(
                "line {line}: Type Error: a table's cells hold one scalar kind — mixing scalar \
                 kinds chooses the dynamic cell (Any), but a table value never rides a cell \
                 (table site #{id})"
            ));
        }
        Ty::Unknown(id)
    }

    pub(super) fn elem_type_of_tbl(&mut self, id: usize) -> Ty {
        if self.lattice.site_elem[id] == Conflict {
            signal!(trace::TRACE_SHAPE_CONFLICT_GUARD);
            return self.report_conflict(id);
        }

        if let Some(children) = self.lattice.child_sites.get(&id).cloned() {
            signal!(trace::TRACE_CHILD_FAST_PATH);
            let mut uniform_type: Option<Ty> = None;

            for &child_id in &children {
                if self.lattice.site_elem[child_id] == Conflict {
                    signal!(trace::TRACE_ELEM_CHILD_CONFLICT);
                    return self.report_conflict(child_id);
                }

                let child_ty = self.elem_type_of_tbl(child_id);

                let child_pending = matches!(child_ty, Ty::Unknown(_));
                match &uniform_type {
                    None => {
                        signal!(trace::TRACE_ELEM_CHILD_FIRST);
                        uniform_type = Some(child_ty.clone());
                    }
                    Some(expected) => {
                        let expected_pending = matches!(expected, Ty::Unknown(_));
                        if !child_pending && !expected_pending && *expected != child_ty {
                            signal!(trace::TRACE_ELEM_CHILD_MISMATCH);
                            return self.report_conflict(child_id);
                        }
                        if expected_pending && !child_pending {
                            uniform_type = Some(child_ty.clone());
                        }
                        signal!(trace::TRACE_ELEM_CHILD_MATCH);
                    }
                }
            }

            if let Some(ty) = uniform_type {
                signal!(trace::TRACE_ELEM_CHILD_UNIFORM);
                return Ty::Tbl(Box::new(ty));
            }
        }

        signal!(trace::TRACE_FALLBACK_RESOLVE);
        match self.lattice.site_elem[id].clone() {
            Tbl(inner) => {
                signal!(trace::TRACE_ELEM_FALLBACK_TBL);
                Ty::Tbl(Box::new(self.materialize_elem(&inner, id)))
            }
            Int => {
                signal!(trace::TRACE_ELEM_FALLBACK_INT);
                Int
            }
            Pending => {
                signal!(trace::TRACE_ANALYZE_PENDING);
                Ty::Unknown(id)
            }
            Flt => {
                signal!(trace::TRACE_ELEM_FALLBACK_FLT);
                Flt
            }
            Bool => {
                signal!(trace::TRACE_ELEM_FALLBACK_BOOL);
                Bool
            }
            Str => {
                signal!(trace::TRACE_ELEM_FALLBACK_STR);
                Str
            }
            Any => Any,
            Ffi => Ffi,
            FfiLib => FfiLib,
            Coro => Coro,
            Ty::Unknown(_) => unreachable!(
                "site_elem holds no nominal unknowns — the walk mints none; unknowns live in \
                 the constraint store"
            ),
            Conflict => {
                signal!(trace::TRACE_ELEM_FALLBACK_CONFLICT);
                self.report_conflict(id)
            }
        }
    }

    /// The NESTED-elem materialization (was `ty_to_static`, the language
    /// bridge — the bridge is gone, the policy stays): identity on every
    /// decided kind, a nested Pending rides as a fresh ghost Unknown, a
    /// nested Conflict reports and rides as `Unknown(site)`.
    fn materialize_elem(&mut self, ty: &Ty, site: usize) -> Ty {
        match ty {
            Int => {
                signal!(trace::TRACE_TY_STATIC_INT);
                Int
            }
            Pending => {
                signal!(trace::TRACE_TY_STATIC_PENDING);
                let ghost = self.lattice.ghost_next;
                self.lattice.ghost_next -= 1;
                Ty::Unknown(ghost)
            }
            Flt => {
                signal!(trace::TRACE_TY_STATIC_FLT);
                Flt
            }
            Bool => {
                signal!(trace::TRACE_TY_STATIC_BOOL);
                Bool
            }
            Str => {
                signal!(trace::TRACE_TY_STATIC_STR);
                Str
            }
            Any => Any,
            Ffi => Ffi,
            FfiLib => FfiLib,
            Coro => Coro,
            Tbl(inner) => {
                signal!(trace::TRACE_TY_STATIC_TBL);
                Ty::Tbl(Box::new(self.materialize_elem(inner, site)))
            }
            Ty::Unknown(_) => unreachable!(
                "site_elem holds no nominal unknowns — the walk mints none; unknowns live in \
                 the constraint store"
            ),
            Conflict => {
                signal!(trace::TRACE_TY_STATIC_CONFLICT);
                self.report_conflict(site)
            }
        }
    }
}

pub(super) fn propagate_elem_down(
    elems: &mut [Ty],
    child_sites: &BTreeMap<usize, BTreeSet<usize>>,
    site: usize,
) {
    let Ty::Tbl(elem) = elems[site].clone() else {
        return;
    };
    if matches!(*elem, Ty::Unknown(_)) {
        return;
    }
    if let Some(children) = child_sites.get(&site) {
        for &child in children {
            if matches!(elems[child], Ty::Unknown(_)) {
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
        if matches!(joined, Conflict) && self.lattice.site_elem[site] != joined {
            crate::glm_dbgln!(
                "[decide] site {site}: {:?} -> Conflict (vt={:?})",
                self.lattice.site_elem[site],
                vt
            );
        }
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
            for (nm, ts) in scope.iter_mut() {
                // Only bindings that ARE the table (or are still Pending) may
                // adopt the table shape. A pinned scalar here is a cell read
                // (dot access or index) that merely rides the table's sites
                // for row-lifetime tracking — overwriting Int with Tbl(Int)
                // makes the later scope-merge join Int + Tbl(Int) = Conflict.
                if ts.aliases.contains(&site)
                    && !is_root(&site)
                    && (ts.ty == Pending || matches!(ts.ty, Tbl(_)))
                    && ts.ty != expected_var_ty
                {
                    crate::glm_dbgln!(
                        "[decide-rewrite] site {site}: '{nm}' {:?} -> {:?} (vt={:?})",
                        ts.ty,
                        expected_var_ty,
                        vt
                    );
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
