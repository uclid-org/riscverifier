#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Error {
    // Specification parser errors
    SpecParseError(String),
}