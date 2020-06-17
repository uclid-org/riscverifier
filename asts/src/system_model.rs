use crate::ast::*;
use crate::utils;

/// ========== Constants ==========================================
pub const PC_VAR: &'static str = "pc";
pub const RETURNED_FLAG: &'static str = "returned";
pub const MEM_VAR: &'static str = "mem";
pub const PRIV_VAR: &'static str = "current_priv";
pub const A0: &'static str = "a0";
pub const SP: &'static str = "sp";
pub const RA: &'static str = "ra";

/// ====================== SYSTEM STATE VARIABLES AND TYPES =================
pub fn pc_type(xlen: u64) -> Type {
    bv_type(xlen)
}
pub fn returned_type() -> Type {
    bv_type(1)
}
pub fn priv_type() -> Type {
    bv_type(2)
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
