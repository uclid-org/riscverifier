use crate::ir::*;

/// Translator error
#[derive(Debug)]
pub struct TErr {
    pub msg: String,
}

/// Deprecated translator error
#[derive(Debug)]
pub struct NoSuchModelError {
    pub error_msg: String,
}

// DWARF reader error
#[derive(Debug)]
pub struct NoSuchDwarfFieldError {}

// Utility functions
pub fn is_var(e: &Expr) -> bool {
    match e {
        Expr::Var(v) => true,
        _ => false,
    }
}

pub fn is_block(e: &Stmt) -> bool {
    match e {
        Stmt::Block(v) => true,
        _ => false,
    }
}

pub fn hex_str_to_u64(numeric: &str) -> Result<u64, std::num::ParseIntError> {
    Ok(u64::from_str_radix(numeric, 16)?)
}

pub fn hex_str_to_i64(numeric: &str) -> Result<i64, std::num::ParseIntError> {
    Ok(i64::from_str_radix(numeric, 16)?)
}

pub fn dec_str_to_u64(numeric: &str) -> Result<u64, std::num::ParseIntError> {
    Ok(u64::from_str_radix(numeric, 10)?)
}

pub fn dec_str_to_i64(numeric: &str) -> Result<i64, std::num::ParseIntError> {
    Ok(i64::from_str_radix(numeric, 10)?)
}

pub fn indent_text(s: String, indent: usize) -> String {
    let spaces = format!("\n{:indent$}", " ", indent = indent);
    format!(
        "{:indent$}{}",
        " ",
        s.replace("\n", &spaces[..]),
        indent = indent
    )
}

pub const INST_LENGTH: u64 = 4;
