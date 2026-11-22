use super::super::constraints::UnknownStore;
use super::{Checker, Frame, WalkSnap};
use crate::diag::Diagnostic;
use crate::shape::ty::Ty;
use crate::shape::{BOUNDARY_ROOT, MOVED_ROOT, is_ghost, is_root, join_ty};
use std::collections::{BTreeMap, BTreeSet};

impl Checker {
    pub(super) fn begin_scope(&mut self) {
        self.frames.push(Frame {
            types: BTreeMap::new(),
            fns: BTreeMap::new(),
            born: BTreeSet::new(),
            captures: BTreeSet::new(),
        });
    }
    pub(super) fn end_scope(&mut self) {
        // (L6 receipt: mirror's omni watcher reads the dying frame's
        // fn faces here — the burial law, its `born` birthplaces, and
        // the rescue tiers. The watcher returns with omni.)
        self.frames.pop();
    }

    pub(super) fn declare_var(
        &mut self,
        lat: &UnknownStore,
        name: String,
        ty: Ty,
    ) -> Result<(), Diagnostic> {
        if let Some(frame) = self.frames.last_mut() {
            // A capture view is not a binding — a body decl over it is
            // the shadow the judge sees (v4: `local x` inside the
            // expansion), not a duplicate. The view dies here; the
            // fresh binding takes the slot.
            if frame.types.contains_key(&name) && !frame.captures.contains(&name) {
                return Err(Diagnostic::scope(format!(
                    "variable '{}' already declared in this scope",
                    name
                )));
            }
            frame.captures.remove(&name);
            frame.types.insert(name, ty);
            return Ok(());
        }
        let boundary_seed = name == "arg";
        if !boundary_seed
            && (self.snap.binds.contains_key(&name)
                || self.top.contains_key(&name)
                || self.cur_decls.contains(&name))
        {
            return Err(Diagnostic::scope(format!(
                "variable '{}' already declared in this scope",
                name
            )));
        }
        self.cur_decls.insert(name.clone());
        let (view, _) = self.view_type(lat, &name, &self.decl_snap);
        if view != Some(ty.clone()) {
            self.top.insert(name, ty);
        }
        Ok(())
    }

    pub(super) fn active_env(&self) -> Option<&BTreeMap<String, Ty>> {
        self.expansion_envs.last()?.as_ref()
    }

    pub(super) fn active_env_override(&self, name: &str) -> Option<Ty> {
        if self.expansion_envs.last()?.is_some() {
            self.env_overrides.last()?.get(name).cloned()
        } else {
            None
        }
    }

    pub(super) fn active_env_face(&self, name: &str) -> Option<Ty> {
        if let Some(face) = self.active_env() {
            face.get(name).cloned()
        } else {
            None
        }
    }

    pub(super) fn call_through_base(&self) -> usize {
        self.expansion_envs
            .iter()
            .rposition(|e| e.is_some())
            .map(|i| self.expansion_frame_bases[i])
            .unwrap_or(0)
    }

    pub(super) fn frames_resolve(&self, name: &str) -> Option<Ty> {
        let base = self.call_through_base();
        self.frames[base..]
            .iter()
            .rev()
            .find_map(|f| f.types.get(name).cloned())
    }

    pub(super) fn var_type(
        &mut self,
        lat: &mut UnknownStore,
        name: &str,
    ) -> Result<Ty, Diagnostic> {
        if let Some(ty) = self.frames_resolve(name) {
            return Ok(lat.resolve(&ty));
        }
        if let Some(ty) = self.active_env_override(name) {
            return Ok(ty);
        }
        if let Some(ty) = self.active_env_face(name) {
            return Ok(ty);
        }
        if let Some(ty) = self.top.get(name) {
            return Ok(lat.resolve(ty));
        }
        let (view, seed_read) = self.view_type(lat, name, &self.snap);
        if seed_read {
            self.seed_read = true;
        }
        view.ok_or_else(|| {
            Diagnostic::scope(format!("reference to undeclared variable '{}'", name))
        })
    }

    /// The depth-0 tier of `var_type`: resolves straight from the root
    /// projection (`top` / the walk snapshot), skipping every frame.
    /// The boundary-root scope is the base of every stack the checker
    /// and lowerer ever hold, so a depth-0 capture reads the SAME
    /// binding from any expansion site — this is the type-level twin
    /// of the lowerer's capture-slot redirect. A creation-site or
    /// call-site same-name shadow must never lend its type to the
    /// face (v2's mint-inside-shadow, t1's shadowed direct expansion).
    pub(super) fn var_type_depth0(
        &mut self,
        lat: &mut UnknownStore,
        name: &str,
    ) -> Result<Ty, Diagnostic> {
        if let Some(ty) = self.top.get(name) {
            return Ok(lat.resolve(ty));
        }
        let (view, seed_read) = self.view_type(lat, name, &self.snap);
        if seed_read {
            self.seed_read = true;
        }
        view.ok_or_else(|| {
            Diagnostic::scope(format!("reference to undeclared variable '{}'", name))
        })
    }

    /// The binding at its recorded WALK depth — the face and capture
    /// view resolution for ALL depths, closing the checker/lowerer
    /// split (Bug 4's surface): the face's type and the lowerer's
    /// `read_var_at` now read the same binding by construction. The
    /// frames stack mirrors the walk scopes minus the root (root
    /// decls live in `top`, not a frame), so walk depth d >= 1 reads
    /// `frames[d - 1]` positionally — the same standing invariant the
    /// mint's `read_var_at` already trusts on the definer's
    /// continuation. A miss keeps the dynamic read: a surface that
    /// did not reconstruct the definer's chain still resolves
    /// innermost, exactly as today.
    pub(super) fn var_type_at_depth(
        &mut self,
        lat: &mut UnknownStore,
        name: &str,
        depth: usize,
    ) -> Result<Ty, Diagnostic> {
        if depth == 0 {
            return self.var_type_depth0(lat, name);
        }
        if let Some(frame) = self.frames.get(depth - 1)
            && let Some(ty) = frame.types.get(name)
        {
            return Ok(lat.resolve(ty));
        }
        self.var_type(lat, name)
    }

    pub(super) fn var_type_callable(&mut self, lat: &mut UnknownStore, name: &str) -> Option<Ty> {
        if let Some(ty) = self.frames_resolve(name) {
            return Some(lat.resolve(&ty));
        }
        if let Some(ty) = self.active_env_override(name) {
            return Some(ty);
        }
        if let Some(ty) = self.active_env_face(name) {
            return Some(ty);
        }
        if let Some(ty) = self.top.get(name) {
            return Some(lat.resolve(ty));
        }
        let (view, seed_read) = self.view_type(lat, name, &self.snap);
        if seed_read {
            self.seed_read = true;
        }
        view.map(|t| lat.resolve(&t))
    }

    fn view_type(&self, lat: &UnknownStore, name: &str, snap: &WalkSnap) -> (Option<Ty>, bool) {
        let fn_binding = self
            .frames
            .iter()
            .rev()
            .find_map(|f| f.fns.get(name).copied())
            .or_else(|| snap.fns.get(name).copied());
        if let Some(Some(ptr)) = fn_binding
            && let Some(id) = lat.fn_value_node(ptr)
        {
            return (Some(lat.resolve(&Ty::Unknown(id))), false);
        }
        let Some(bind) = snap.binds.get(name) else {
            return (None, false);
        };
        if name == "arg" && bind.aliases.contains(&BOUNDARY_ROOT) {
            let id = lat.boundary_seed();
            let resolved = lat.resolve(&Ty::Unknown(id));
            let seed_read = matches!(resolved, Ty::Unknown(_));
            return (Some(Ty::Tbl(Box::new(resolved))), seed_read);
        }
        if bind.aliases.contains(&MOVED_ROOT)
            && let Some(sites) = snap.severed.get(name)
            && !sites.is_empty()
        {
            let mut elem = Ty::Pending;
            for &s in sites {
                if !is_root(&s) && !is_ghost(&s) {
                    let site_view = lat.resolve(&self.ctx.elems[s]);
                    elem = join_ty(&elem, &site_view);
                }
            }
            return (Some(Ty::Tbl(Box::new(elem))), false);
        }
        if let Some(&id) = snap.scalars.get(name) {
            return (
                Some(match &bind.ty {
                    Ty::Tbl(_) => Ty::Tbl(Box::new(lat.resolve(&Ty::Unknown(id)))),
                    _ => lat.resolve(&Ty::Unknown(id)),
                }),
                false,
            );
        }
        match &bind.ty {
            Ty::Tbl(live_elem) => {
                let mut elem = Ty::Pending;
                for &s in bind.aliases.iter() {
                    if !is_root(&s) && !is_ghost(&s) {
                        let site_view = lat.resolve(&self.ctx.elems[s]);
                        elem = join_ty(&elem, &site_view);
                    }
                }
                if matches!(elem, Ty::Pending) {
                    elem = live_elem.as_ref().clone();
                }
                (Some(Ty::Tbl(Box::new(elem))), false)
            }
            other => (Some(other.clone()), false),
        }
    }

    pub(super) fn write_back(&mut self, name: &str, ty: Ty) {
        if let Some(frame) = self
            .frames
            .iter_mut()
            .rev()
            .find(|f| f.types.contains_key(name))
        {
            frame.types.insert(name.to_string(), ty);
        } else {
            self.top.insert(name.to_string(), ty);
        }
    }

    pub(super) fn hold_entry(&mut self, name: &str, ty: Ty) {
        if let Some(frame) = self
            .frames
            .iter_mut()
            .rev()
            .find(|f| f.types.contains_key(name))
        {
            frame.types.insert(name.to_string(), ty);
        } else if !self.top.contains_key(name) {
            self.top.insert(name.to_string(), ty);
        }
    }
}
