// TODO: Rewrite parser to read the binary

use std::process::Command;

use std::collections::{HashMap, HashSet};

use std::rc::Rc;

use pest::Parser;

use std::fmt;

use crate::utils;

#[derive(Parser)]
#[grammar = "pest/objectdump.pest"]
pub struct ObjectDumpReader;

impl ObjectDumpReader {
    pub fn get_binary_object_dump(
        binary_file_paths: &Vec<&str>,
    ) -> HashMap<u64, Vec<AssemblyLine>> {
        let mut assembly_lines: Vec<AssemblyLine>;
        let mut seen_functions: HashSet<String>;
        let mut function_blocks: HashMap<u64, Vec<AssemblyLine>> = HashMap::new();
        for binary_file_path in binary_file_paths {
            assembly_lines = vec![];
            seen_functions = HashSet::new(); // FIXME: Assumes that binary function definitions are disjoint!
            function_blocks = HashMap::new();
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
                                let mut func_offset_iter =
                                    assembly_line_iter.next().unwrap().into_inner();
                                let func_name =
                                    func_offset_iter.next().unwrap().as_str().to_string();
                                let func_offset_str = func_offset_iter.as_str();
                                let func_offset =
                                    utils::hex_str_to_u64(func_offset_str.trim_start_matches("0x"))
                                        .unwrap_or_else(|_| 0);
                                // instruction op code
                                let op_code = assembly_line_iter
                                    .next()
                                    .unwrap()
                                    .into_inner()
                                    .as_str()
                                    .to_string()
                                    .replace(".", "_");
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
                                            let reg = InstOperand::Register(operand_value.as_str().to_string(), None);
                                            operands.push(reg);
                                        }
                                        Rule::offset_operand => {
                                            let mut offset_operand_iter = operand_value.into_inner();
                                            let offset = utils::dec_str_to_i64(offset_operand_iter.next().unwrap().as_str()).expect("[get_binary_object_dump] Unable to parse offset in instruction arugment");
                                            let reg = InstOperand::Register(offset_operand_iter.as_str().to_string(), Some(offset));
                                            operands.push(reg);
                                        }
                                        _ => {
                                            panic!("[get_binary_object_dump] Unexpected RISC-V instruction argument {:#?}.", operand_value.as_rule())
                                        }
                                    }
                                }
                                if seen_functions.get(&func_name).is_none()
                                    && !&assembly_lines.is_empty()
                                {
                                    // Sanity check
                                    let _ = assembly_lines.iter().map(|al| {
                                        assert!(
                                            al.function_name() == assembly_lines[0].function_name(),
                                            "Invalid function block."
                                        )
                                    });
                                    // Add list of assembly lines to function blocks
                                    function_blocks.insert(
                                        assembly_lines[0].address.clone(),
                                        assembly_lines.clone(),
                                    );
                                    assembly_lines = vec![];
                                    seen_functions.insert(func_name.clone());
                                }
                                if seen_functions.len() == 0 {
                                    seen_functions.insert(func_name.clone());
                                }
                                // debug!(
                                //     "[get_binary_object_dump]   Addr: {:?}, Function name: {:?}, Offset: {:?}, OpCode: {:?}, Arguments: {:?}.",
                                //     address, func_name, func_offset, op_code, operands
                                // );
                                assembly_lines.push(AssemblyLine {
                                    address,
                                    func_name,
                                    func_offset,
                                    op_code,
                                    operands,
                                });
                            }
                            Err(_e) => {
                                // FIXME: Handle this instead of failing silently
                                // warn!(
                                //     "Error parsing object dump line {:?}. {:?}",
                                //     &line.replace("\t", " ")[..],
                                //     e
                                // );
                            }
                        }
                    }
                    if assembly_lines.len() > 0 {
                        function_blocks
                            .insert(assembly_lines[0].address.clone(), assembly_lines.clone());
                    }
                }
                Err(e) => {
                    panic!("[get_binary_object_dump] Unable to convert object dump output to UTF-8 string: {:?}", e);
                }
            }
        }
        function_blocks
    }

    pub fn get_cfg(func_blk: Vec<Rc<AssemblyLine>>) -> Cfg {
        if func_blk.len() == 0 {
            return Cfg::new(0);
        }
        let mut cfg = Cfg::new(func_blk[0].address);
        // Stores basic block ENTRY point addresses
        let mut marked = HashSet::new();
        let mut blk_entry_addr = None;
        // Iterate over the assembly lines in the function block and create dependencies for the cfg
        // Mark all of the addresses which are the beginning of a basic block (except the first function entry basic block)
        for al in &func_blk {
            if blk_entry_addr.is_none() {
                blk_entry_addr = Some(al.address());
            }
            // DEP1. Instruction is branch, add fall through addr
            // MARK1. branch fall through targets
            // DEP2. Instruction is branch | jal, add absolute addr
            // MARK2. absolute jump (branch) targets
            // FIXME: Handle jalr and mret
            match &al.op_code[..] {
                "beq" | "bne" | "blt" | "bge" | "bltu" | "jal" => {
                    let next_addr = Cfg::next_addr(al.address());
                    // Add the fall through address only if it's inside the function
                    // and the first register is not zero (this would be a unconditional
                    // jump that doesn't return). If it's not "zero" nor "ra", throw
                    // and error because we currently can't compute where it will go
                    if func_blk
                        .iter()
                        .find(|rc_al| rc_al.address() == next_addr)
                        .is_some()
                    {
                        match &al.op_code[..] {
                            "jal" => {
                                match &al.rd().expect(&format!("Invalid jump instruction {:#?}.", al)).get_reg_name()[..] {
                                    "zero" => (),
                                    "ra" => cfg.add_next_blk_addr(blk_entry_addr.unwrap(), next_addr),
                                    _ => panic!("Invalid first argument for jal. Unable to determine the address after the jump."),
                                }
                            }
                            "beq" | "bne" | "blt" | "bge" | "bltu" => {
                                cfg.add_next_blk_addr(blk_entry_addr.unwrap(), next_addr)
                            }
                            _ => panic!("Unsupported jump instruction."),
                        }
                        marked.insert(next_addr);
                    }
                    let jump_addr = al.imm().unwrap().get_imm_val() as u64;
                    cfg.add_abs_jump_addr(blk_entry_addr.unwrap(), jump_addr);
                    marked.insert(jump_addr);
                }
                "jalr" | "mret" => {
                    // Only add the next address to split the block.
                    // We don't know where it jumps statically so we don't mark any "jump_addr".
                    let next_addr = Cfg::next_addr(al.address());
                    marked.insert(next_addr);
                }
                _ => (),
            }
            // DEP3. Update blk_entry_addr
            match &al.op_code[..] {
                "beq" | "bne" | "blt" | "bge" | "bltu" | "jal" | "jalr" | "mret" => {
                    blk_entry_addr = Some(Cfg::next_addr(al.address()))
                }
                _ => (),
            }
        }
        // Create basic blocks
        //  If addr is marked, then save the
        //  previous vector as a basic block
        //  and start a new vector of instructions
        let mut basic_blk: Vec<Rc<AssemblyLine>> = vec![];
        for al in &func_blk {
            if marked.get(&al.address()).is_some() && basic_blk.len() > 0 {
                let entry_addr = basic_blk[0].address();
                cfg.add_basic_blk(BasicBlock::new(entry_addr, basic_blk));
                basic_blk = vec![];
            }
            basic_blk.push(Rc::clone(al));
        }
        // Add the last to cfg
        if basic_blk.len() > 0 {
            cfg.add_basic_blk(BasicBlock::new(basic_blk[0].address(), basic_blk));
        }
        cfg
    }
}

#[derive(Debug)]
pub struct Cfg {
    /// Entry address for the function represented by the CFG
    entry_addr: u64,
    /// Map from basic block entry address to a BasicBlock
    basic_blks_map: HashMap<u64, BasicBlock>,
    /// Map from entry addresses to entry addresses.
    /// Only entry addresses whose corresponding basic block ends in a jump or branch
    /// with an absolute target will have a key and value pair in this map.
    abs_jump_map: HashMap<u64, u64>,
    /// Map from addresses to addresses.
    /// Map of address to the next fall through address
    next_blk_addr_map: HashMap<u64, u64>,
}
impl Cfg {
    pub fn new(entry_addr: u64) -> Self {
        Cfg {
            entry_addr,
            basic_blks_map: HashMap::new(),
            abs_jump_map: HashMap::new(),
            next_blk_addr_map: HashMap::new(),
        }
    }
    /// Returns the next fall through address
    pub fn next_blk_addr(&self, addr: u64) -> Option<&u64> {
        self.next_blk_addr_map.get(&addr)
    }
    /// Returns the jump address (if it's a branch/jump instruction)
    pub fn next_abs_jump_addr(&self, addr: u64) -> Option<&u64> {
        self.abs_jump_map.get(&addr)
    }
    /// Returns the entry address to the cfg
    pub fn get_entry_addr(&self) -> &u64 {
        &self.entry_addr
    }
    /// Returns the basic block at that address
    #[allow(dead_code)]
    pub fn get_basic_blk(&self, addr: u64) -> Option<&BasicBlock> {
        self.basic_blks_map.get(&addr)
    }
    /// Returns the map of basic blocks
    pub fn bbs(&self) -> &HashMap<u64, BasicBlock> {
        &self.basic_blks_map
    }
    /// Finds and returns all cycles starting starting with current node
    pub fn find_cycle(
        &self,
        current_node: &u64,
        seen_nodes: &mut HashSet<u64>,
        processed_cycle: &mut bool,
    ) -> Option<Vec<u64>> {
        if seen_nodes.contains(current_node) {
            return Some(vec![*current_node]);
        }
        seen_nodes.insert(*current_node);
        if let Some(addr) = self.next_blk_addr(*current_node) {
            if let Some(mut cycle) = self.find_cycle(addr, seen_nodes, processed_cycle) {
                if !*processed_cycle {
                    cycle.push(*current_node);
                }
                if cycle[0] == *current_node {
                    *processed_cycle = true;
                }
                return Some(cycle);
            }
        }
        if let Some(addr) = self.next_abs_jump_addr(*current_node) {
            if let Some(mut cycle) = self.find_cycle(addr, seen_nodes, processed_cycle) {
                if !*processed_cycle {
                    cycle.push(*current_node);
                }
                if cycle[0] == *current_node {
                    *processed_cycle = true;
                }
                return Some(cycle);
            }
        }
        seen_nodes.remove(current_node);
        None
    }
    /// Helpers
    pub fn add_basic_blk(&mut self, bb: BasicBlock) {
        self.basic_blks_map.insert(bb.entry_addr, bb);
    }
    pub fn add_next_blk_addr(&mut self, from_addr: u64, to_addr: u64) {
        self.next_blk_addr_map.insert(from_addr, to_addr);
    }
    pub fn add_abs_jump_addr(&mut self, from_addr: u64, to_addr: u64) {
        self.abs_jump_map.insert(from_addr, to_addr);
    }
    pub fn next_addr(addr: u64) -> u64 {
        addr + utils::INST_LENGTH
    }
}

#[derive(Debug)]
pub struct BasicBlock {
    entry_addr: u64,
    insts: Vec<Rc<AssemblyLine>>,
}

impl BasicBlock {
    pub fn new(entry_addr: u64, insts: Vec<Rc<AssemblyLine>>) -> Self {
        BasicBlock { entry_addr, insts }
    }
    pub fn insts(&self) -> &Vec<Rc<AssemblyLine>> {
        &self.insts
    }
}

#[derive(Debug, Clone)]
pub struct AssemblyLine {
    address: u64,
    func_name: String,
    func_offset: u64,
    op_code: String,
    operands: Vec<InstOperand>,
}

impl AssemblyLine {
    pub fn address(&self) -> u64 {
        self.address
    }

    pub fn function_name(&self) -> &str {
        &self.func_name[..]
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

    #[allow(dead_code)]
    pub fn offset(&self) -> Option<i64> {
        match &self.op_code[..] {
            "jalr" | "lb" | "lh" | "lw" | "lbu" | "lhu" | "lwu" | "ld" | "sb" | "sh" | "sw"
            | "sd" => {
                assert!(self.operands.len() == 2);
                match &self.operands[1] {
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
