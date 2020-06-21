#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    NoSuchDwarfFieldError,
    CouldNotFindDwarfChild,
    CouldNotFindType,
    MissingVar(String),
    MissingFuncSig(String),
}
