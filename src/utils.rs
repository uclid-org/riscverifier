#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    // Dwarf reader errors
    NoSuchDwarfFieldError,
    CouldNotFindDwarfChild,
    // Translator errors
    TErr { msg: String },
    // Specification parser errors
    SpecParseError(String),
}

// Utility functions
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

/// Constants
pub const INST_LENGTH: u64 = 4;
