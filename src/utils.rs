pub fn hex_str_to_u64(numeric: &str) -> u64 {
    u64::from_str_radix(numeric, 16).unwrap()
}

pub fn hex_str_to_i64(numeric: &str) -> i64 {
    i64::from_str_radix(numeric, 16).unwrap()
}

pub fn dec_str_to_u64(numeric: &str) -> u64 {
    u64::from_str_radix(numeric, 10).unwrap()
}

pub fn dec_str_to_i64(numeric: &str) -> i64 {
    i64::from_str_radix(numeric, 10).unwrap()
}
