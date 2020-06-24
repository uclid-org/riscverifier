#[macro_use]
extern crate lalrpop_util;
lalrpop_mod!(pub riscv_spec_lang, "/spec_lang/riscv_spec_lang.rs"); // synthesized by LALRPOP

pub mod veriv_ast;
pub mod spec_lang;
mod utils;
