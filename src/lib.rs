#![allow(clippy::missing_safety_doc)]

pub mod rt;
pub mod trace;

impl AlmElem {
    pub fn kind(self) -> i32 {
        rt::arg_kind_of(&self)
    }
}

pub use rt::{AnyWord, alm_any_pack, classify_word};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AlmElem {
    Integer,
    Float,
    Boolean,
    String,
    Any,
}
