use std::process::Command;

use pest::Parser;

use crate::utils;

#[derive(Parser)]
#[grammar = "objectdump.pest"]
pub struct ObjectDumpParser;

impl ObjectDumpParser {
    pub fn get_binary_object_dump(binary_file_paths: &Vec<String>) -> Vec<AssemblyLine> {
        let mut assembly_lines = vec![];
        for binary_file_path in binary_file_paths {
            let output = Command::new("riscv64-unknown-elf-objdump")
                .arg("-d")
                .arg("-M no-aliases")
                .arg("--prefix-addresses")
                .arg(binary_file_path)
                .output()
                .expect("Failed process.");
            match String::from_utf8(output.stdout) {
                Ok(v) => {
                    for line in v.lines() {
                        match ObjectDumpParser::parse(
                            Rule::assembly_line,
                            &line.replace("\t", " ")[..],
                        ) {
                            Ok(mut result) => {
                                debug!(
                                    "[get_binary_object_dump] Result parsed: {:?}.",
                                    &line.replace("\t", " ")[..]
                                );
                                let mut assembly_line_iter = result.next().unwrap().into_inner();
                                // assembly line address
                                let address = utils::hex_str_to_u64(
                                    assembly_line_iter.next().unwrap().as_str(),
                                );
                                // callee name and offset
                                let mut callee_offset_iter =
                                    assembly_line_iter.next().unwrap().into_inner();
                                let callee_name =
                                    callee_offset_iter.next().unwrap().as_str().to_string();
                                let callee_offset_str =
                                    callee_offset_iter.as_str().trim_start_matches("0x");
                                let callee_offset = if !callee_offset_str.is_empty() {
                                    utils::hex_str_to_u64(callee_offset_str)
                                } else {
                                    0
                                };
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
                                            operands.push(InstOperand::Immediate(utils::dec_str_to_i64(operand_value.as_str())));
                                        }
                                        Rule::hexidecimal => {
                                            let without_prefix_hex = operand_value.as_str().trim_start_matches("0x");
                                            operands.push(InstOperand::Immediate(utils::hex_str_to_i64(without_prefix_hex)));
                                        }
                                        Rule::hexidecimal_without_prefix => {
                                            operands.push(InstOperand::Immediate(utils::hex_str_to_i64(operand_value.as_str())));
                                        }
                                        Rule::ident => {
                                            operands.push(InstOperand::Register(operand_value.as_str().to_string(), 0));
                                        }
                                        Rule::offset_operand => {
                                            let mut offset_operand_iter = operand_value.into_inner();
                                            let offset = utils::dec_str_to_i64(offset_operand_iter.next().unwrap().as_str());
                                            let register = offset_operand_iter.as_str().to_string();
                                            operands.push(InstOperand::Register(register, offset));
                                        }
                                        _ => {
                                            panic!("[get_binary_object_dump] Unexpected RISC-V instruction argument {:#?}.", operand_value.as_rule())
                                        }
                                    }
                                }
                                debug!(
                                    "[get_binary_object_dump]   Addr: {:?}, Function name: {:?}, Offset: {:?}, OpCode: {:?}, Arguments: {:?}.",
                                    address, callee_name, callee_offset, op_code, operands
                                );
                                assembly_lines.push(AssemblyLine {
                                    address,
                                    callee_name,
                                    callee_offset,
                                    op_code,
                                    operands,
                                });
                            }
                            Err(e) => {
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
        assembly_lines
    }
}

#[derive(Debug)]
pub enum InstOperand {
    Register(String, i64),
    Immediate(i64),
}

#[derive(Debug)]
pub struct AssemblyLine {
    address: u64,
    callee_name: String,
    callee_offset: u64,
    op_code: String,
    operands: Vec<InstOperand>,
}
