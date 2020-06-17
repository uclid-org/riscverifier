#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    // Specification parser errors
    SpecParseError(String),
}

pub const BYTE_SIZE: u64 = 8;