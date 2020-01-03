use std::process::Command;

use std::collections::{HashMap, HashSet};

use pest::Parser;

use std::fmt;

use crate::utils;

#[derive(Parser)]
#[grammar = "pest/objectdump.pest"]
pub struct ObjectDumpReader;

impl ObjectDumpReader {
    pub fn get_binary_object_dump(
        binary_file_paths: &Vec<String>,
    ) -> HashMap<u64, Vec<AssemblyLine>> {
        let mut assembly_lines: Vec<AssemblyLine> = vec![];
        let mut seen_functions: HashSet<String> = HashSet::new();
        let mut function_blocks: HashMap<u64, Vec<AssemblyLine>> = HashMap::new();
        for binary_file_path in binary_file_paths {
            let output = Command::new("riscv64-unknown-elf-objdump")
                .arg("-d")
                .arg("-M no-aliases")
                .arg("--prefix-addresses")
                .arg(binary_file_path)
                .output()
                .expect("[get_binary_object_dump] Failed to run process using riscv64-unknown-elf-objdump binary.");
            match String::from_utf8(output.stdout) {
                Ok(v) => {
                    for line in v.lines() {
                        match ObjectDumpReader::parse(
                            Rule::assembly_line,
                            &line.replace("\t", " ")[..],
                        ) {
                            Ok(mut result) => {
                                // debug!(
                                //     "[get_binary_object_dump] Result parsed: {:?}.",
                                //     &line.replace("\t", " ")[..]
                                // );
                                let mut assembly_line_iter = result.next().unwrap().into_inner();
                                // assembly line address
                                let address = utils::hex_str_to_u64(
                                    assembly_line_iter.next().unwrap().as_str(),
                                ).expect("[get_binary_object_dump] Unable to parse assembly line address.");
                                // callee name and offset
                                let mut callee_offset_iter =
                                    assembly_line_iter.next().unwrap().into_inner();
                                let callee_name =
                                    callee_offset_iter.next().unwrap().as_str().to_string();
                                let callee_offset_str = callee_offset_iter.as_str();
                                let callee_offset = utils::hex_str_to_u64(
                                    callee_offset_str.trim_start_matches("0x"),
                                )
                                .unwrap_or_else(|_| 0);
                                // instruction op code
                                let op_code = assembly_line_iter
                                    .next()
                                    .unwrap()
                                    .into_inner()
                                    .as_str()
                                    .to_string();
                                // instruction operands
                                let mut operands = vec![];
                                while let Some(operand_iter) = assembly_line_iter.next() {
                                    let operand_value = operand_iter.into_inner().next().unwrap();
                                    match operand_value.as_rule() {
                                        Rule::decimal | Rule::neg_decimal => {
                                            let imm = InstOperand::Immediate(utils::dec_str_to_i64(operand_value.as_str()).expect("[get_binary_object_dump] Unable to parse instruction argument as decimal."));
                                            operands.push(imm);
                                        }
                                        Rule::hexidecimal => {
                                            let without_prefix_hex = operand_value.as_str().trim_start_matches("0x");
                                            let imm = InstOperand::Immediate(utils::hex_str_to_i64(without_prefix_hex).expect("[get_binary_object_dump] Unable to parse instruction argument as hexidecimal."));
                                            operands.push(imm);
                                        }
                                        Rule::absolute_addr => {
                                            let imm = InstOperand::Immediate(utils::hex_str_to_i64(operand_value.as_str()).expect("[get_binary_object_dump] Unable to parse instruction argument as hexidecimal (without prefix)."));
                                            operands.push(imm);
                                        }
                                        Rule::ident => {
                                            let reg = InstOperand::Register(operand_value.as_str().to_string(), 0);
                                            operands.push(reg);
                                        }
                                        Rule::offset_operand => {
                                            let mut offset_operand_iter = operand_value.into_inner();
                                            let offset = utils::dec_str_to_i64(offset_operand_iter.next().unwrap().as_str()).expect("[get_binary_object_dump] Unable to parse offset in instruction arugment");
                                            let reg = InstOperand::Register(offset_operand_iter.as_str().to_string(), offset);
                                            operands.push(reg);
                                        }
                                        _ => {
                                            panic!("[get_binary_object_dump] Unexpected RISC-V instruction argument {:#?}.", operand_value.as_rule())
                                        }
                                    }
                                }
                                if seen_functions.len() == 0 {
                                    seen_functions.insert(callee_name.clone());
                                }
                                if seen_functions.get(&callee_name).is_none()
                                    && !&assembly_lines.is_empty()
                                {
                                    function_blocks.insert(
                                        assembly_lines[0].address.clone(),
                                        assembly_lines.clone(),
                                    );
                                    assembly_lines = vec![];
                                    seen_functions.insert(callee_name.clone());
                                }
                                // debug!(
                                //     "[get_binary_object_dump]   Addr: {:?}, Function name: {:?}, Offset: {:?}, OpCode: {:?}, Arguments: {:?}.",
                                //     address, callee_name, callee_offset, op_code, operands
                                // );
                                assembly_lines.push(AssemblyLine {
                                    address,
                                    callee_name,
                                    callee_offset,
                                    op_code,
                                    operands,
                                });
                            }
                            Err(e) => {
                                // TODO: Handle this instead of failing silently
                                warn!(
                                    "Error parsing object dump line {:?}. {:?}",
                                    &line.replace("\t", " ")[..],
                                    e
                                );
                            }
                        }
                    }
                }
                Err(e) => {
                    panic!("[get_binary_object_dump] Unable to convert object dump output to UTF-8 string: {:?}", e);
                }
            }
        }
        function_blocks.insert(assembly_lines[0].address.clone(), assembly_lines.clone());
        function_blocks
    }
}

#[derive(Debug, Clone)]
pub enum InstOperand {
    Register(String, i64),
    Immediate(i64),
}

impl fmt::Display for InstOperand {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            InstOperand::Register(reg_id, _offset) => {
                // match offset {
                // 0 => write!(f, "{}", reg_id),
                // _ => write!(f, "{}+{}", reg_id, offset),

                // }
                write!(f, "{}", reg_id)
            }
            InstOperand::Immediate(imm) => write!(f, "{}", imm),
        }
    }
}

#[derive(Debug, Clone)]
pub struct AssemblyLine {
    address: u64,
    callee_name: String,
    callee_offset: u64,
    op_code: String,
    operands: Vec<InstOperand>,
}

impl AssemblyLine {
    pub fn address(&self) -> u64 {
        self.address
    }

    pub fn function_name(&self) -> &str {
        &self.callee_name[..]
    }

    pub fn base_instruction_name(&self) -> &str {
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
            | "csrrw" | "csrrs" | "csrrc" => Some(&self.operands[0]),
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
            | "lhu" | "lwu" | "ld" | "sb" | "sh" | "sw" | "sd" => Some(&self.operands[1]),
            "fence" | "sfence" | "beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu" => {
                Some(&self.operands[0])
            }
            "csrrw" | "csrrs" | "csrrc" => Some(&self.operands[2]),
            _ => None,
        }
    }

    pub fn rs2(&self) -> Option<&InstOperand> {
        match &self.op_code[..] {
            "add" | "sub" | "sll" | "slt" | "sltu" | "xor" | "srl" | "sra" | "or" | "and"
            | "addw" | "subw" | "sllw" | "srlw" | "sraw" | "mul" | "mulh" | "mulhsu" | "mulhu"
            | "div" | "divu" | "rem" | "remu" | "mulw" | "divw" | "divuw" | "remw" | "remuw" => {
                Some(&self.operands[2])
            }
            "sb" | "sh" | "sw" | "sd" => Some(&self.operands[0]),
            "beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu" => Some(&self.operands[1]),
            _ => None,
        }
    }

    pub fn offset(&self) -> Option<i64> {
        match &self.op_code[..] {
            "jalr" | "lb" | "lh" | "lw" | "lbu" | "lhu" | "lwu" | "ld" | "sb" | "sh" | "sw"
            | "sd" => {
                assert!(self.operands.len() == 2);
                match &self.operands[1] {
                    InstOperand::Register(_register_id, offset) => Some(*offset),
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
            | "bgeu" | "csrrwi" | "csrrsi" | "csrrci" => Some(&self.operands[2]),
            "lui" | "auipc" | "jal" => Some(&self.operands[1]),
            _ => None,
        }
    }

    pub fn csr(&self) -> Option<&InstOperand> {
        match &self.op_code[..] {
            "csrrwi" | "csrrsi" | "csrrci" | "csrrw" | "csrrs" | "csrrc" => Some(&self.operands[1]),
            _ => None,
        }
    }
}
