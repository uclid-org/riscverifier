#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    // Dwarf reader errors
    NoSuchDwarfFieldError,
    CouldNotFindDwarfChild,
    CouldNotFindType,
    MissingVar(String),
    MissingFuncSig(String),
}

pub const BYTE_SIZE: u64 = 8;

