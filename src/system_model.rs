use std::collections::HashSet;

use crate::ir::{Type, Var};
use crate::utils;

/// ========== Constants ==========================================
pub const PC_VAR: &'static str = "pc";
pub const RETURNED_FLAG: &'static str = "returned";
pub const MEM_VAR: &'static str = "mem";
pub const PRIV_VAR: &'static str = "current_priv";
pub const EXCEPT_VAR: &'static str = "exception";
pub const SP: &'static str = "sp";
pub const RA: &'static str = "ra";
pub const A0: &'static str = "a0";
pub const SYSTEM_VARS: [&'static str; 7] =
    [PC_VAR, RETURNED_FLAG, MEM_VAR, PRIV_VAR, EXCEPT_VAR, SP, RA];

/// ====================== SYSTEM STATE VARIABLES AND TYPES =================
/// The set of system state variables
pub fn pc_var(xlen: u64) -> Var {
    Var {
        name: PC_VAR.to_string(),
        typ: bv_type(xlen),
    }
}
/// Returned flag indicates if jalr has occured.
/// We assume all jalr return to the caller.
pub fn returned_var() -> Var {
    Var {
        name: RETURNED_FLAG.to_string(),
        typ: bv_type(1),
    }
}
/// Memory state variable
pub fn mem_var(xlen: u64) -> Var {
    Var {
        name: MEM_VAR.to_string(),
        typ: mem_type(xlen),
    }
}
/// Privilege state variable
pub fn priv_var() -> Var {
    Var {
        name: PRIV_VAR.to_string(),
        typ: bv_type(2),
    }
}
/// Expection state variable
pub fn except_var(xlen: u64) -> Var {
    Var {
        name: EXCEPT_VAR.to_string(),
        typ: bv_type(xlen),
    }
}
/// A vector of the state variables
pub fn sys_state_vars(xlen: u64) -> HashSet<Var> {
    let mut vec_var = HashSet::new();
    vec_var.insert(pc_var(xlen));
    vec_var.insert(returned_var());
    vec_var.insert(mem_var(xlen));
    vec_var.insert(priv_var());
    vec_var.insert(except_var(xlen));
    vec_var
}
/// Returns the type of memory (XLEN addressable byte valued array)
pub fn mem_type(xlen: u64) -> Type {
    Type::Array {
        in_typs: vec![Box::new(bv_type(xlen))],
        out_typ: Box::new(bv_type(utils::BYTE_SIZE)),
    }
}
/// Returns a bitvector type of specified width
pub fn bv_type(width: u64) -> Type {
    Type::Bv { w: width }
}
pub fn system_var_type(name: &str, xlen: u64) -> Type {
    match name {
        PC_VAR => pc_var(xlen).typ,
        RETURNED_FLAG => returned_var().typ,
        MEM_VAR => mem_type(xlen),
        PRIV_VAR => priv_var().typ,
        EXCEPT_VAR => except_var(xlen).typ,
        SP => Type::Bv { w: xlen },
        _ => panic!("Unable to determine type for {}.", name),
    }
}
