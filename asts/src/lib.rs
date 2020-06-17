extern crate dwarf_ctx;

#[macro_use]
extern crate lalrpop_util;
lalrpop_mod!(pub riscv_spec_lang, "/spec_lang/riscv_spec_lang.rs"); // synthesized by LALRPOP

pub mod ast;
pub mod spec_lang;
mod system_model;
mod utils;
