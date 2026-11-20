use super::type_name::type_name;
use crate::ast::NodeId;
use crate::diag::Diagnostic;
use crate::shape::Ty;
use std::collections::BTreeMap;

/// The constraint store. (L4 receipt: `unify` and the fn-value node
/// minters are the checker's unification lane — they ride the walk's
/// store now and wake when the checker ports; the walk itself only
/// binds through the pins' `bind`.)
pub(super) struct UnknownStore {
    subs: BTreeMap<usize, Ty>,
    next_id: usize,
    boundary_seed: Option<usize>,
    fn_ret_nodes: BTreeMap<NodeId, usize>,
    #[allow(dead_code)]
    fn_value_nodes: BTreeMap<NodeId, usize>,
}

impl UnknownStore {
    pub(super) fn new() -> Self {
        let mut store = Self {
            subs: BTreeMap::new(),
            next_id: usize::MAX,
            boundary_seed: None,
            fn_ret_nodes: BTreeMap::new(),
            fn_value_nodes: BTreeMap::new(),
        };
        store.boundary_seed = Some(store.mint_id());
        store
    }

    fn mint_id(&mut self) -> usize {
        let id = self.next_id;
        self.next_id -= 1;
        id
    }

    #[allow(dead_code)]
    pub(super) fn fresh(&mut self) -> Ty {
        Ty::Unknown(self.mint_id())
    }

    pub(super) fn boundary_seed(&self) -> usize {
        self.boundary_seed
            .expect("the store construction mints the seed")
    }

    pub(super) fn ensure_fn_ret(&mut self, fn_ptr: NodeId) -> usize {
        if let Some(&id) = self.fn_ret_nodes.get(&fn_ptr) {
            return id;
        }
        let id = self.mint_id();
        self.fn_ret_nodes.insert(fn_ptr, id);
        id
    }

    pub(super) fn fn_ret_node(&self, fn_ptr: NodeId) -> Option<usize> {
        self.fn_ret_nodes.get(&fn_ptr).copied()
    }

    #[allow(dead_code)]
    pub(super) fn ensure_fn_value(&mut self, fn_ptr: NodeId) -> usize {
        if let Some(&id) = self.fn_value_nodes.get(&fn_ptr) {
            return id;
        }
        let id = self.mint_id();
        self.fn_value_nodes.insert(fn_ptr, id);
        id
    }

    #[allow(dead_code)]
    pub(super) fn fn_value_node(&self, fn_ptr: NodeId) -> Option<usize> {
        self.fn_value_nodes.get(&fn_ptr).copied()
    }

    pub(super) fn next_id(&self) -> usize {
        self.next_id
    }

    pub(super) fn take_subs(&mut self) -> BTreeMap<usize, Ty> {
        std::mem::take(&mut self.subs)
    }

    pub(super) fn resolve(&self, ty: &Ty) -> Ty {
        match ty {
            Ty::Unknown(id) => match self.subs.get(id) {
                Some(resolved) => self.resolve(resolved),
                None => ty.clone(),
            },
            Ty::Tbl(inner) => Ty::Tbl(Box::new(self.resolve(inner))),
            other => other.clone(),
        }
    }

    fn occurs(&self, id: usize, ty: &Ty) -> bool {
        match ty {
            Ty::Unknown(other) => {
                *other == id
                    || self
                        .subs
                        .get(other)
                        .is_some_and(|bound| self.occurs(id, bound))
            }
            Ty::Tbl(inner) => self.occurs(id, inner),
            _ => false,
        }
    }

    pub(super) fn bind(&mut self, id: usize, ty: Ty) -> Result<(), Diagnostic> {
        if self.occurs(id, &ty) {
            return Err(Diagnostic::ty(
                "cyclic table type — a table's element type \
                 may not contain the table itself (alm's element types are finite)",
            ));
        }
        self.subs.insert(id, ty);
        Ok(())
    }

    #[allow(dead_code)]
    pub(super) fn unify(&mut self, expected: &Ty, actual: &Ty) -> Result<(), Diagnostic> {
        let expected = self.resolve(expected);
        let actual = self.resolve(actual);
        match (&expected, &actual) {
            (a, b) if a == b => Ok(()),

            (Ty::Unknown(id_a), Ty::Unknown(id_b)) if id_a != id_b => {
                self.bind(*id_b, Ty::Unknown(*id_a))
            }

            (Ty::Unknown(_), _) | (_, Ty::Unknown(_)) => {
                let (u_id, c_ty) = match (&expected, &actual) {
                    (Ty::Unknown(id), ty) => (*id, ty.clone()),
                    (ty, Ty::Unknown(id)) => (*id, ty.clone()),
                    _ => unreachable!(),
                };
                self.bind(u_id, c_ty)
            }

            (Ty::Tbl(e1), Ty::Tbl(e2)) => self.unify(e1, e2),

            (Ty::Closure(a), Ty::Closure(b)) if a != b => Err(Diagnostic::ty(
                "divergent expansions cannot meet at one call",
            )),

            _ => Err(Diagnostic::ty(format!(
                "type conflict — {} vs {}",
                type_name(&expected),
                type_name(&actual)
            ))),
        }
    }
}
