#[derive(Debug)]
pub struct NoSuchModelError {
    pub error_msg: String,
}

#[derive(Debug)]
pub struct NoSuchDwarfFieldError {}

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
