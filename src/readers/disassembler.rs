//! A disassembler for RISC-V binaries.
//! NOTE: For research purposes, we have defered the engineering of
//! the disassembler. We are currently relying on the objdump to
//! disassemble the binary for us and parsing a very specific
//! format of the objdump output.

use pest::Parser;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::fs::File;
use std::io::prelude::*;
use std::process::Command;
use std::rc::Rc;

use crate::utils;

/// FIXME: Create static strings for all instructions below
const BEQ: &'static str = "beq";
const BNE: &'static str = "bne";
const BLT: &'static str = "blt";
const BGE: &'static str = "bge";
const BEQZ: &'static str = "beqz";
const BLTU: &'static str = "bltu";
const JAL: &'static str = "jal";
const JALR: &'static str = "jalr";
const MRET: &'static str = "mret";
const DIR_JUMP_OPS: [&'static str; 7] = [BEQ, BNE, BLT, BGE, BEQZ, BLTU, JAL];
const JUMP_OPS: [&'static str; 9] = [BEQ, BNE, BLT, BGE, BEQZ, BLTU, JAL, JALR, MRET];

#[derive(Parser)]
#[grammar = "pest/objectdump.pest"]
struct ObjectDumpParser;

pub struct Disassembler<'a> {
    /// Disassembler to use. Supports an objectdump disassembler for now.
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
        // A set of all processed functions.
        let mut processed = HashSet::new();
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
                    als.push(Rc::new(AssemblyLine {
                        addr,
                        func,
                        offset,
                        op_code,
                        ops,
                    }));
                } else {
                    if let Some(mut file) = self.debug_file.as_ref() {
                        file.write_all(line.as_bytes());
                    }
                }
            }
        }
        als
    }
    // / Creates CFGs given a list of assembly lines.
    // fn als_to_cfgs(als: &Vec<AssemblyLine>) -> HashMap<>;
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
        let next_addr = self.address() + utils::INST_LENGTH;
        if self.is_dir_jump() {
            // Add the fallthrough address
            match self.op() {
                // ASSUMPTION: Jal instructions with "ra" as the destination
                // register is assumed to return.
                JAL => {
                    if self.rd().unwrap().get_reg_name() == "ra" {
                        succs.push(next_addr)
                    }
                }
                // Branches and other instructions can always fall through
                _ => succs.push(next_addr),
            }
            // Add the target address
            let target_addr = self.imm().unwrap().get_imm_val();
            succs.push(target_addr as u64);
        } else {
            // Fallthrough address
            succs.push(next_addr);
        }
        succs
    }
}

impl AssemblyLine {
    pub fn function_name(&self) -> &str {
        &self.func[..]
    }

    pub fn op(&self) -> &str {
        match &self.op_code[..] {
            // TODO: What to do with fences?
            "fence.vma" | "sfence.vma" | "sfence" => &"fence",
            _ => &self.op_code[..],
        }
    }

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

    #[allow(dead_code)]
    pub fn offset(&self) -> Option<i64> {
        match &self.op_code[..] {
            "jalr" | "lb" | "lh" | "lw" | "lbu" | "lhu" | "lwu" | "ld" | "sb" | "sh" | "sw"
            | "sd" => {
                assert!(self.ops.len() == 2);
                match &self.ops[1] {
                    InstOperand::Register(_register_id, offset) => {
                        Some(offset.expect("Instruction has no offset!"))
                    }
                    _ => panic!("[offset] Operand has no offset!"),
                }
            }
            _ => None,
        }
    }

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
            InstOperand::Register(n, _i) => n.clone(),
            _ => panic!("Not a register operand!"),
        }
    }
    pub fn get_reg_offset(&self) -> i64 {
        match self {
            InstOperand::Register(_n, i) => i.expect("Register has no offset."),
            _ => panic!("Not a register operand!"),
        }
    }
    pub fn has_offset(&self) -> bool {
        match self {
            InstOperand::Register(_n, i) => i.is_some(),
            _ => panic!("Not a register operand!"),
        }
    }
}
