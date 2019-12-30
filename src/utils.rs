use std::collections::HashMap;

use crate::objectdumpreader::InstOperand;

#[derive(Debug)]
pub struct InvalidFormatError;

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

// TODO: Computes a CFG from the function
pub fn compute_cfg(function: &Vec<u64>) -> Result<HashMap<u64, Vec<u64>>, InvalidFormatError> {
    Ok(HashMap::new())
}
// TODO: Topologically sort
pub fn topological_sort(cfg: &HashMap<u64, Vec<u64>>) -> Result<Vec<u64>, InvalidFormatError> {
    Ok(vec![])
}
