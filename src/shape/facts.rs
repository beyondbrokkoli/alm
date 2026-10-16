use super::core::LayoutVerdict;
use crate::ast::{Expr, StaticType, Stmt};
use glm_rt::{signal, trace};
use std::collections::{BTreeMap, BTreeSet};

#[derive(Clone, PartialEq, Debug)]
pub enum Keep {
    Name(String),
    #[allow(dead_code)]
    Ghost(usize),
}

#[derive(Clone)]
pub struct DoExitFree {
    #[allow(dead_code)]
    pub site: usize,
    pub carrier: String,
    pub keeps: Vec<Keep>,
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum TagSrc {
    If(*const Stmt),
    Call(*const Expr),
}

#[derive(Clone)]
pub struct ArmFreeEntry {
    pub carrier: String,
    pub tag: TagSrc,
    pub nothing_on: bool,
    pub keeps: Vec<Keep>,
}

#[derive(Clone)]
pub struct FnDef {
    pub params: Vec<String>,
    pub body: *const [Stmt],
    pub ret: StaticType,
    pub signature: Option<Vec<StaticType>>,
}

impl FnDef {
    pub unsafe fn body(&self) -> &[Stmt] {
        unsafe { &*self.body }
    }
}

#[derive(Clone)]
pub struct ShapeFacts {
    pub sites: BTreeMap<*const Expr, usize>,
    pub elems: Vec<StaticType>,
    pub boundary_elem: Option<StaticType>,
    #[allow(dead_code)]
    pub layouts: Vec<LayoutVerdict>,
    pub free_sites: BTreeSet<*const Stmt>,
    pub free_keeps: BTreeMap<*const Stmt, Vec<Keep>>,
    pub do_exit_frees: BTreeMap<(*const Stmt, u8), Vec<DoExitFree>>,
    pub root_exit_frees: Vec<DoExitFree>,
    pub stmt_temp_frees: BTreeMap<*const Stmt, Vec<usize>>,
    pub cond_temp_frees: BTreeMap<*const Stmt, Vec<usize>>,
    pub arm_temp_frees: BTreeMap<*const Expr, Vec<usize>>,
    pub ret_path_frees: BTreeMap<*const Stmt, Vec<DoExitFree>>,
    pub ret_path_keep_frees: BTreeMap<*const Stmt, Vec<DoExitFree>>,
    pub ret_path_keep_temps: BTreeMap<*const Stmt, Vec<usize>>,
    pub rebind_frees: BTreeMap<*const Stmt, BTreeMap<String, Vec<Keep>>>,
    pub join_tags: BTreeMap<*const Stmt, bool>,
    pub call_tags: BTreeMap<*const Expr, Vec<bool>>,
    pub store_ghost_keeps: BTreeMap<*const Stmt, Vec<usize>>,
    pub ctor_ghost_keeps: BTreeMap<*const Expr, Vec<(usize, usize)>>,
    pub arm_free_sites: BTreeMap<*const Stmt, Vec<ArmFreeEntry>>,
    pub arm_rebind_frees: BTreeMap<*const Stmt, Vec<ArmFreeEntry>>,
    pub arm_do_exit_frees: BTreeMap<(*const Stmt, u8), Vec<ArmFreeEntry>>,
    pub arm_root_exit_frees: Vec<ArmFreeEntry>,
    pub move_poisons: BTreeMap<*const Stmt, BTreeSet<String>>,
    pub name_dense: BTreeMap<(String, usize), bool>,
    pub stored_ctor_parents: BTreeSet<usize>,
    pub substitutions: BTreeMap<usize, StaticType>,
    pub local_types: BTreeMap<(*const Stmt, String), StaticType>,
    pub row_reads: BTreeMap<usize, (String, usize)>,
    pub cell_children: BTreeMap<usize, BTreeSet<usize>>,
    pub fn_scope_keys: BTreeMap<*const Expr, (*const Stmt, u8)>,
    pub fn_touched: BTreeMap<*const Expr, BTreeSet<String>>,
    pub fn_defs: BTreeMap<*const Expr, FnDef>,
    pub call_defs: BTreeMap<*const Expr, *const Expr>,
    pub stmt_lines: BTreeMap<*const Stmt, usize>,
    pub ctor_lines: Vec<usize>,
    pub adopt_lines: BTreeMap<String, usize>,
    pub diagnostics: Vec<String>,
}

impl ShapeFacts {
    pub fn elem_of(&self, ctor: &Expr) -> StaticType {
        let id = self.sites[&(ctor as *const Expr)];
        let elem = self.elems[id].clone();
        self.resolve_elem_type(elem)
    }

    fn resolve_elem_type(&self, ty: StaticType) -> StaticType {
        match &ty {
            StaticType::Unknown(id) => match self.substitutions.get(id) {
                Some(resolved) => self.resolve_elem_type(resolved.clone()),
                None => ty,
            },
            StaticType::Table(inner) => {
                let resolved = self.resolve_elem_type((**inner).clone());
                StaticType::Table(Box::new(resolved))
            }
            _ => ty,
        }
    }

    pub fn is_dense_at_depth(&self, name: &str, depth: usize) -> bool {
        self.name_dense
            .get(&(name.to_string(), depth))
            .copied()
            .unwrap_or(false)
    }

    pub fn check_row_reads(&mut self) {
        let reads: Vec<(usize, String, usize)> = self
            .row_reads
            .iter()
            .map(|(&base, (name, depth))| (base, name.clone(), *depth))
            .collect();
        let mut reported: BTreeSet<usize> = BTreeSet::new();
        for (base, name, depth) in reads {
            let mut level: BTreeSet<usize> =
                self.cell_children.get(&base).cloned().unwrap_or_default();
            for _pierce in 2..=depth {
                let mut next: BTreeSet<usize> = BTreeSet::new();
                for row in level {
                    if reported.insert(row)
                        && matches!(
                            self.resolve_elem_type(self.elems[row].clone()),
                            StaticType::Unknown(_)
                        )
                    {
                        signal!(trace::TRACE_ANALYZE_MISSING_VALUE);
                        let line = self.ctor_lines[row];
                        self.diagnostics.push(format!(
                            "line {line}: Type Error: a row of '{name}' is read before it is \
                             ever given a value (table site #{row})"
                        ));
                    }
                    if let Some(kids) = self.cell_children.get(&row) {
                        next.extend(kids.iter().copied());
                    }
                }
                level = next;
            }
        }
    }

    pub fn is_free(&self, stmt: &Stmt) -> bool {
        self.free_sites.contains(&(stmt as *const Stmt))
    }
}
