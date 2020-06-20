/// =========================================================================
/// # Constants
pub const PRELUDE_PATH: &str = "models/prelude.ucl";

/// =========================================================================
/// # Macros
#[macro_export]
macro_rules! set {
    ( $( $x:expr ),* ) => {  // Match zero or more comma delimited items
        {
            let mut temp_set = HashSet::new();  // Create a mutable HashSet
            $(
                temp_set.insert($x); // Insert each item matched into the HashSet
            )*
            temp_set // Return the populated HashSet
        }
    };
}

/// =========================================================================
/// # Conversion helper functions

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

/// =========================================================================
/// # Printing helper functions

/// Returns the string with spce indentation
pub fn indent_text(s: String, indent: usize) -> String {
    let spaces = format!("\n{:indent$}", " ", indent = indent);
    format!(
        "{:indent$}{}",
        " ",
        s.replace("\n", &spaces[..]),
        indent = indent
    )
}

/// =========================================================================
/// # Translated variable renaming

pub fn global_var_ptr_name(name: &str) -> String {
    format!("global_var_{}", name)
}
pub fn global_func_addr_name(func_name: &str) -> String {
    format!("global_func_{}", func_name)
}



