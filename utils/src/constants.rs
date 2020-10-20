/// ## Size constants
pub const BYTE_SIZE: u64 = 8;   // There are 8 bits in a byte
pub const INST_LENGTH_IN_BYTES: u64 = 4; // Instructions are 4 bytes long

/// ## System variable names
pub const PC_VAR: &'static str = "pc";
pub const RETURNED_FLAG: &'static str = "returned";
pub const MEM_VAR_B: &'static str = "mem_b";
pub const MEM_VAR_H: &'static str = "mem_h";
pub const MEM_VAR_W: &'static str = "mem_w";
pub const MEM_VAR_D: &'static str = "mem_d";
pub const PRIV_VAR: &'static str = "current_priv";
pub const A0: &'static str = "a0";
pub const SP: &'static str = "sp";
pub const RA: &'static str = "ra";

/// ## Instruction constants
/// FIXME: Create static strings for all instructions below
pub const BEQ: &'static str = "beq";
pub const BNE: &'static str = "bne";
pub const BLT: &'static str = "blt";
pub const BGE: &'static str = "bge";
pub const BEQZ: &'static str = "beqz";
pub const BLTU: &'static str = "bltu";
pub const JAL: &'static str = "jal";
pub const JALR: &'static str = "jalr";
pub const MRET: &'static str = "mret";
pub const FENCE: &'static str = "fence";
pub const SFENCE_VMA: &'static str = "sfence.vma";
pub const FENCE_I: &'static str = "fence.i";
pub const DIR_JUMP_OPS: [&'static str; 7] = [BEQ, BNE, BLT, BGE, BEQZ, BLTU, JAL];
pub const JUMP_OPS: [&'static str; 9] = [BEQ, BNE, BLT, BGE, BEQZ, BLTU, JAL, JALR, MRET];
pub const IGNORED_INSTS: [&'static str; 3] = [FENCE, SFENCE_VMA, FENCE_I];