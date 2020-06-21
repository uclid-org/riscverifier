//! A disassembler for RISC-V binaries.
//! NOTE: For research purposes, we have defered the engineering of
//! the disassembler. We are currently relying on the objdump to
//! disassemble the binary for us and parsing a very specific
//! format of the objdump output.

use pest::Parser;
use std::collections::HashSet;
use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::process::Command;
use std::rc::Rc;

use rv_model::system_model::INST_LENGTH_IN_BYTES;

use crate::utils;

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

#[derive(Parser)]
#[grammar = "pest/objectdump.pest"]
struct ObjectDumpParser;

pub struct Disassembler<'a> {
    /// Disassembler as a command line (CL) option.
    /// Only supports using an CL objectdump disassembler.
    /// I suggest you don't change this and try to use the default.
    ///
    /// # EXAMPLE: riscv64-unknown-elf-objdump
    cmd: Option<&'a str>,
    /// Prints debugging information the file if provided.
    debug_file: Option<File>,
}

impl<'a> Disassembler<'a> {
    /// Constructor
    pub fn new(cmd: Option<&'a str>, debug_fp: Option<&'a str>) -> Self {
        Disassembler {
            cmd,
            debug_file: debug_fp.map_or(None, |fp| File::create(fp).ok()),
        }
    }
    /// Creates a process to call objdump and disassembles the
    /// given binaries.
    pub fn read_binaries(&mut self, paths: &Vec<&str>) -> Vec<Rc<AssemblyLine>> {
        // Assembly lines from the binaries (at the paths).
        let mut als = vec![];
        // A set of all processed addresses.
        let mut processed = HashSet::new();
        // Accumulate assembly lines
        let mut raw_als_data = vec![];
        // Iterate over the bianry paths and process them one by one.
        for path in paths {
            // Call the objdump to disassemble the binary at `path`.
            let cmd = self.cmd.map_or("riscv64-unknown-elf-objdump", |v| v);
            let objdump = Command::new(cmd)
                .arg("-d")
                .arg("-M no-aliases")
                .arg("--prefix-addresses")
                .arg(path)
                .output()
                .expect("Disassembler process failed.");
            // Read the std output
            let stdout = String::from_utf8(objdump.stdout)
                .expect(&format!("Unable to read objdump of {}.", path));
            // Parse each instruction line individually
            for line in stdout.lines() {
                if let Ok(mut result) =
                    ObjectDumpParser::parse(Rule::assembly_line, &line.replace("\t", " ")[..])
                {
                    let mut al_iter = result.next().unwrap().into_inner();
                    let addr_str = al_iter.next().unwrap().as_str();
                    // Unmangle address
                    let addr = utils::hex_str_to_u64(addr_str)
                        .expect(&format!("Invalid assembly line address {}.", addr_str));
                    assert!(
                        processed.get(&addr).is_none(),
                        format!("Found two instructions at address {}", &addr)
                    );
                    // Mark this address as processed
                    processed.insert(addr);
                    // Get function name and offset iter
                    let mut al_iter_inner = al_iter.next().unwrap().into_inner();
                    // Unmangle function name
                    let func = al_iter_inner.next().unwrap().as_str().to_string();
                    // Unmangle function offset
                    let offset_str = al_iter_inner.as_str().trim_start_matches("0x");
                    // FIXME: Default 0 if we can't parse it
                    let offset = utils::hex_str_to_u64(offset_str).unwrap_or_else(|_| 0);
                    // Unmangle op code
                    let op_code = al_iter.next().unwrap().into_inner().as_str().to_string();
                    if IGNORED_INSTS.contains(&&op_code[..]) {
                        continue;
                    }
                    // Unmangle operands
                    let mut ops = vec![];
                    while let Some(operand_iter) = al_iter.next() {
                        let operand_value = operand_iter.into_inner().next().unwrap();
                        match operand_value.as_rule() {
                                Rule::decimal | Rule::neg_decimal => {
                                    let imm = InstOperand::Immediate(utils::dec_str_to_i64(operand_value.as_str()).expect("[get_binary_object_dump] Unable to parse instruction argument as decimal."));
                                    ops.push(imm);
                                }
                                Rule::hexidecimal => {
                                    let without_prefix_hex = operand_value.as_str().trim_start_matches("0x");
                                    let imm = InstOperand::Immediate(utils::hex_str_to_i64(without_prefix_hex).expect("[get_binary_object_dump] Unable to parse instruction argument as hexidecimal."));
                                    ops.push(imm);
                                }
                                Rule::absolute_addr => {
                                    let imm = InstOperand::Immediate(utils::hex_str_to_i64(operand_value.as_str()).expect("[get_binary_object_dump] Unable to parse instruction argument as hexidecimal (without prefix)."));
                                    ops.push(imm);
                                }
                                Rule::ident => {
                                    let reg = InstOperand::Register(operand_value.as_str().to_string(), None);
                                    ops.push(reg);
                                }
                                Rule::offset_operand => {
                                    let mut offset_operand_iter = operand_value.into_inner();
                                    let offset = utils::dec_str_to_i64(offset_operand_iter.next().unwrap().as_str()).expect("[get_binary_object_dump] Unable to parse offset in instruction arugment");
                                    let reg = InstOperand::Register(offset_operand_iter.as_str().to_string(), Some(offset));
                                    ops.push(reg);
                                }
                                _ => {
                                    panic!("[get_binary_object_dump] Unexpected RISC-V instruction argument {:#?}.", operand_value.as_rule())
                                }
                            }
                    }
                    raw_als_data.push((addr, func, offset, op_code, ops));
                } else {
                    if let Some(mut file) = self.debug_file.as_ref() {
                        file.write_all(line.as_bytes())
                            .expect("Unable to write to debug file.");
                    }
                }
            }
        }
        // A set of processed functions.
        // FIXME: Heuristic to determine if a line is the entry of a function
        let mut processed_func = HashSet::new();
        let raw_als_data_enum = raw_als_data.iter().enumerate().collect::<Vec<_>>();
        for (index, (addr, func, offset, op_code, ops)) in &raw_als_data_enum {
            // Add function to processed set
            let is_entry = !processed_func.contains(&func[..]);
            processed_func.insert(func.clone());
            // It's an exit if it's the last instruction or the next instruction is defined for another function
            let is_exit = index + 1 >= raw_als_data_enum.len()
                || !processed_func.contains(&(raw_als_data_enum[index + 1].1).1[..]);
            als.push(Rc::new(AssemblyLine {
                is_entry,
                is_exit,
                addr: *addr,
                func: func.to_owned(),
                offset: *offset,
                op_code: op_code.to_owned(),
                ops: ops.to_owned(),
            }));
        }
        als
    }
}

pub trait Inst {
    /// Address of the instruction
    fn address(&self) -> u64;
    /// Is a direct jump
    fn is_dir_jump(&self) -> bool;
    /// Is a jump instruction
    fn is_jump(&self) -> bool;
    /// Is a indirect jump
    fn is_ind_jump(&self) -> bool {
        self.is_jump() && !self.is_dir_jump()
    }
    /// Successors given by ID / addresses
    fn successors(&self) -> Vec<u64>;
}

#[derive(Debug, Clone)]
pub struct AssemblyLine {
    is_entry: bool,
    is_exit: bool,
    /// Instruction address
    addr: u64,
    /// Function that the instruction resides in
    func: String,
    /// Offset of the instruction from the entry of the function
    offset: u64,
    /// Op code of the instruction
    op_code: String,
    /// Operands of the fuction
    ops: Vec<InstOperand>,
}

impl fmt::Display for AssemblyLine {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(
            f,
            "{:#x?}:{:?}: {:?} {}",
            self.addr,
            self.func,
            self.op_code,
            self.ops
                .iter()
                .map(|o| o.to_string())
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl Inst for AssemblyLine {
    fn address(&self) -> u64 {
        self.addr
    }
    fn is_dir_jump(&self) -> bool {
        DIR_JUMP_OPS.contains(&self.op())
    }
    fn is_jump(&self) -> bool {
        JUMP_OPS.contains(&self.op())
    }
    fn successors(&self) -> Vec<u64> {
        let mut succs = vec![];
        let next_addr = self.address() + INST_LENGTH_IN_BYTES;
        if self.is_dir_jump() {
            // Add the fallthrough address
            match self.op() {
                // ASSUMPTION: Jal instructions with "ra" as the destination
                // register is assumed to return.
                JAL => {
                    if self.rd().unwrap().get_reg_name() == "ra" && !self.is_exit {
                        succs.push(next_addr)
                    }
                }
                // Branches and other instructions can always fall through
                _ => succs.push(next_addr),
            }
            // Add the target address
            let target_addr = self.imm().unwrap().get_imm_val();
            succs.push(target_addr as u64);
        } else if !self.is_ind_jump() {
            // Fallthrough address
            succs.push(next_addr);
        }
        succs
    }
}

impl AssemblyLine {
    /// Returns true if the line is the entry to the function
    pub fn is_label_entry(&self) -> bool {
        self.is_entry
    }
    /// Returns the function the line is defined at
    pub fn function_name(&self) -> &str {
        &self.func[..]
    }
    /// Returns the op code
    pub fn op(&self) -> &str {
        match &self.op_code[..] {
            // TODO: What to do with fences?
            "fence.vma" | "sfence.vma" | "sfence" => &"fence",
            _ => &self.op_code[..],
        }
    }
    /// Returns the destination register
    pub fn rd(&self) -> Option<&InstOperand> {
        match &self.op_code[..] {
            "add" | "sub" | "sll" | "slt" | "sltu" | "xor" | "srl" | "sra" | "or" | "and"
            | "addw" | "subw" | "sllw" | "srlw" | "sraw" | "mul" | "mulh" | "mulhsu" | "mulhu"
            | "div" | "divu" | "rem" | "remu" | "mulw" | "divw" | "divuw" | "remw" | "remuw"
            | "addi" | "slti" | "sltiu" | "xori" | "ori" | "andi" | "slli" | "srli" | "srai"
            | "addiw" | "slliw" | "srliw" | "sraiw" | "jalr" | "lb" | "lh" | "lw" | "lbu"
            | "lhu" | "lwu" | "ld" | "lui" | "auipc" | "jal" | "csrrwi" | "csrrsi" | "csrrci"
            | "csrrw" | "csrrs" | "csrrc" => Some(&self.ops[0]),
            _ => None,
        }
    }
    /// Returns rs1
    pub fn rs1(&self) -> Option<&InstOperand> {
        match &self.op_code[..] {
            "add" | "sub" | "sll" | "slt" | "sltu" | "xor" | "srl" | "sra" | "or" | "and"
            | "addw" | "subw" | "sllw" | "srlw" | "sraw" | "mul" | "mulh" | "mulhsu" | "mulhu"
            | "div" | "divu" | "rem" | "remu" | "mulw" | "divw" | "divuw" | "remw" | "remuw"
            | "addi" | "slti" | "sltiu" | "xori" | "ori" | "andi" | "slli" | "srli" | "srai"
            | "addiw" | "slliw" | "srliw" | "sraiw" | "jalr" | "lb" | "lh" | "lw" | "lbu"
            | "lhu" | "lwu" | "ld" | "sb" | "sh" | "sw" | "sd" => Some(&self.ops[1]),
            "fence" | "sfence" | "beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu" => {
                Some(&self.ops[0])
            }
            "csrrw" | "csrrs" | "csrrc" => Some(&self.ops[2]),
            _ => None,
        }
    }
    /// Returns rs2
    pub fn rs2(&self) -> Option<&InstOperand> {
        match &self.op_code[..] {
            "add" | "sub" | "sll" | "slt" | "sltu" | "xor" | "srl" | "sra" | "or" | "and"
            | "addw" | "subw" | "sllw" | "srlw" | "sraw" | "mul" | "mulh" | "mulhsu" | "mulhu"
            | "div" | "divu" | "rem" | "remu" | "mulw" | "divw" | "divuw" | "remw" | "remuw" => {
                Some(&self.ops[2])
            }
            "sb" | "sh" | "sw" | "sd" => Some(&self.ops[0]),
            "beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu" => Some(&self.ops[1]),
            _ => None,
        }
    }
    /// Returns immediate
    pub fn imm(&self) -> Option<&InstOperand> {
        match &self.op_code[..] {
            "addi" | "slti" | "sltiu" | "xori" | "ori" | "andi" | "slli" | "srli" | "srai"
            | "addiw" | "slliw" | "srliw" | "sraiw" | "beq" | "bne" | "blt" | "bge" | "bltu"
            | "bgeu" | "csrrwi" | "csrrsi" | "csrrci" => Some(&self.ops[2]),
            "lui" | "auipc" | "jal" => Some(&self.ops[1]),
            _ => None,
        }
    }

    pub fn csr(&self) -> Option<&InstOperand> {
        match &self.op_code[..] {
            "csrrwi" | "csrrsi" | "csrrci" | "csrrw" | "csrrs" | "csrrc" => Some(&self.ops[1]),
            _ => None,
        }
    }
}

#[derive(Debug, Clone)]
pub enum InstOperand {
    Register(String, Option<i64>),
    Immediate(i64),
}

impl fmt::Display for InstOperand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            InstOperand::Register(reg_id, _offset) => write!(f, "{}", reg_id),
            InstOperand::Immediate(imm) => write!(f, "{}", imm),
        }
    }
}

impl InstOperand {
    pub fn get_imm_val(&self) -> i64 {
        match self {
            InstOperand::Immediate(i) => *i,
            _ => panic!("Not an immediate operand!"),
        }
    }
    pub fn get_reg_name(&self) -> String {
        match self {
            InstOperand::Register(n, _) => n.clone(),
            _ => panic!("Not a register operand!"),
        }
    }
    pub fn get_reg_offset(&self) -> i64 {
        match self {
            InstOperand::Register(_, i) => i.expect("Register has no offset."),
            _ => panic!("Not a register operand!"),
        }
    }
    pub fn has_offset(&self) -> bool {
        match self {
            InstOperand::Register(_, i) => i.is_some(),
            _ => panic!("Not a register operand!"),
        }
    }
}
