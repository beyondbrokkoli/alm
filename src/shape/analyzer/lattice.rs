use super::*;
impl Analyzer {
    pub(super) fn report_conflict(&mut self, id: usize) -> Ty {
        if self.ledger.conflict_reported.insert(id) {
            let line = self.ctor_lines[id];
            self.ledger.diagnostics.push(
                Diagnostic::ty(format!(
                    "a table's cells hold one scalar kind — mixing scalar \
                     kinds chooses the dynamic cell (Any), but a table value never rides a cell \
                     (table site #{id})"
                ))
                .with_site(Some(line)),
            );
        }
        Ty::Unknown(id)
    }

    pub(super) fn elem_type_of_tbl(&mut self, id: usize) -> Ty {
        if self.lattice.site_elem[id] == Conflict {
            return self.report_conflict(id);
        }

        if let Some(children) = self.lattice.child_sites.get(&id).cloned() {
            let mut uniform_type: Option<Ty> = None;

            for &child_id in &children {
                if self.lattice.site_elem[child_id] == Conflict {
                    return self.report_conflict(child_id);
                }

                let child_ty = self.elem_type_of_tbl(child_id);

                let child_pending = matches!(child_ty, Ty::Unknown(_));
                match &uniform_type {
                    None => {
                        uniform_type = Some(child_ty.clone());
                    }
                    Some(expected) => {
                        let expected_pending = matches!(expected, Ty::Unknown(_));
                        if !child_pending && !expected_pending && *expected != child_ty {
                            return self.report_conflict(child_id);
                        }
                        if expected_pending && !child_pending {
                            uniform_type = Some(child_ty.clone());
                        }
                    }
                }
            }

            if let Some(ty) = uniform_type {
                return Ty::Tbl(Box::new(ty));
            }
        }

        match self.lattice.site_elem[id].clone() {
            Tbl(inner) => Ty::Tbl(Box::new(self.materialize_elem(&inner, id))),
            Int => Int,
            Pending => Ty::Unknown(id),
            Flt => Flt,
            Bool => Bool,
            Str => Str,
            Any => Any,
            Ffi => Ffi,
            FfiLib => FfiLib,
            Async => Async,
            Ty::Closure(_) => unreachable!("a closure face never rides a site elem"),
            Ty::Unknown(_) => unreachable!(
                "site_elem holds no nominal unknowns — the walk mints none; unknowns live in \
                 the constraint store"
            ),
            Conflict => self.report_conflict(id),
        }
    }

    fn materialize_elem(&mut self, ty: &Ty, site: usize) -> Ty {
        match ty {
            Int => Int,
            Pending => {
                let ghost = self.lattice.ghost_next;
                self.lattice.ghost_next -= 1;
                Ty::Unknown(ghost)
            }
            Flt => Flt,
            Bool => Bool,
            Str => Str,
            Any => Any,
            Ffi => Ffi,
            FfiLib => FfiLib,
            Async => Async,
            Ty::Closure(_) => unreachable!("a closure face never rides a site elem"),
            Tbl(inner) => Ty::Tbl(Box::new(self.materialize_elem(inner, site))),
            Ty::Unknown(_) => unreachable!(
                "site_elem holds no nominal unknowns — the walk mints none; unknowns live in \
                 the constraint store"
            ),
            Conflict => self.report_conflict(site),
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
    pub(super) fn decide(&mut self, _rec: Gate, site: usize, vt: &Ty) {
        if self.lattice.site_elem[site] == Conflict {
            return;
        }

        let joined = join_ty(&self.lattice.site_elem[site], vt);
        if matches!(joined, Conflict) && self.lattice.site_elem[site] != joined {
            crate::alm_dbgln!(
                "[decide] site {site}: {:?} -> Conflict (vt={:?})",
                self.lattice.site_elem[site],
                vt
            );
        }
        if self.lattice.site_elem[site] != joined {
            self.lattice.site_elem[site] = joined.clone();
            self.walk.changed = true;
        }

        let expected_var_ty = Tbl(Box::new(self.lattice.site_elem[site].clone()));

        let WalkState {
            scopes, changed, ..
        } = &mut self.walk;
        for scope in scopes.iter_mut() {
            for (nm, ts) in scope.iter_mut() {
                if ts.shape.aliases.contains(&site)
                    && !is_root(&site)
                    && (ts.shape.ty == Pending || matches!(ts.shape.ty, Tbl(_)))
                    && ts.shape.ty != expected_var_ty
                {
                    crate::alm_dbgln!(
                        "[decide-rewrite] site {site}: '{nm}' {:?} -> {:?} (vt={:?})",
                        ts.shape.ty,
                        expected_var_ty,
                        vt
                    );
                    ts.shape.ty = expected_var_ty.clone();
                    if ts.shape.ty != Pending {
                        *changed = true;
                    }
                }
            }
        }
    }
}
