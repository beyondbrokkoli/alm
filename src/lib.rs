#![allow(clippy::missing_safety_doc)]

pub mod rt;
pub mod trace;

impl GlmElem {
    pub fn kind(self) -> i32 {
        rt::arg_kind_of(&self)
    }
}

pub use rt::{AnyWord, classify_word, glm_any_pack};

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum GlmElem {
    Integer,
    Float,
    Boolean,
    String,
    Any,
}
