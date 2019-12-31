use crate::objectdumpreader::{AssemblyLine, InstOperand};

use std::collections::{HashMap, HashSet};

use topological_sort::TopologicalSort;

use crate::utils::*;
use std::fs;
use std::fs::File;
use std::io::prelude::*;

pub struct UclidTranslator<'a> {
    xlen: u64,
    inst_length: u64,
    ignored_functions: &'a HashSet<&'a str>,
    generated_functions: HashSet<u64>,
    import_decls: Vec<String>,
    define_decls: Vec<String>,
    state_var_decls: Vec<String>,
    state_var_ids: HashSet<String>,
    procedures_decls: Vec<String>,
    init_stmts: Vec<String>,
    next_stmts: Vec<String>,
    control_stmts: Vec<String>,
}

impl<'a> UclidTranslator<'a> {
    pub fn create(xlen: u64, ignored_functions: &'a HashSet<&'a str>) -> UclidTranslator<'a> {
        UclidTranslator {
            xlen,
            inst_length: 4,
            ignored_functions,
            generated_functions: HashSet::new(),
            import_decls: vec![],
            define_decls: vec![],
            state_var_decls: vec![],
            state_var_ids: HashSet::new(),
            procedures_decls: vec![],
            init_stmts: vec![],
            next_stmts: vec![],
            control_stmts: vec![],
        }
    }

    pub fn reset_model(&mut self) {
        self.generated_functions = HashSet::new();
        self.import_decls = vec![];
        self.define_decls = vec![];
        self.state_var_decls = vec![];
        self.state_var_ids = HashSet::new();
        self.procedures_decls = vec![];
        self.init_stmts = vec![];
        self.next_stmts = vec![];
        self.control_stmts = vec![];
    }

    pub fn generate_function_model(
        &mut self,
        function_name: &str,
        function_vecs: &HashMap<u64, Vec<AssemblyLine>>,
    ) -> Result<(), NoSuchModelError> {
        let function_entry_addr = UclidTranslator::function_addr_from_name(function_name, function_vecs);
        self.generate_function_model_by_entry_addr(&function_entry_addr, function_vecs, 0);
        Ok(())
    }

    fn generate_function_model_by_entry_addr(
        &mut self,
        function_addr: &u64,
        function_vecs: &HashMap<u64, Vec<AssemblyLine>>,
        level: usize,
    ) -> Result<(), NoSuchModelError> {
        let function_name = UclidTranslator::function_name_from_addr(function_addr, function_vecs);
        if self.ignored_functions.get(&function_name).is_some() {
            debug!("[generate_function_model_by_entry_addr] Ignored function {}.", function_name);
            return Ok(());
        }
        if self.generated_functions.get(&function_addr).is_some() {
            debug!(
                "[generate_function_model] Cyclic function call for function {}.",
                function_name
            );
            return Err(NoSuchModelError { recursive_function: function_name.to_string() });
        } else {
            self.generated_functions.insert(*function_addr);
        }
        // debug!(
        //     "[generate_function_model] {:?}",
        //     function_vec
        //         .iter()
        //         .map(|line| line.base_instruction_name())
        //         .collect::<Vec<_>>()
        // );
        let function_vec = function_vecs
            .get(function_addr)
            .expect("[generate_function_model_by_entry_addr] Invalid function entry address.");

        println!("{}{}", format!("{: <1$}", "", level*2), function_vec[0].function_name());

        self.generate_state_variables(function_vec);
        self.generate_function_atomic_blocks(function_vec);
        let mut ts = TopologicalSort::<String>::new();
        let mut atomic_block_entry_addr: u64 = function_vec[0].address();
        for assembly_line in function_vec {
            let atomic_block_fallthrough_addr = assembly_line.address() + self.inst_length;
            match assembly_line.base_instruction_name() {
                "jal" | "beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu" => {
                    if let InstOperand::Immediate(atomic_block_jump_addr) = assembly_line.imm().expect("[generate_function_model] Unable to find a target address for a jump instruction") {
                        // Add jump target absolute addresses
                        ts.add_dependency(atomic_block_entry_addr.to_string(), atomic_block_jump_addr.to_string());
                        match assembly_line.base_instruction_name() {
                            "beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu"  => {
                                // Add default fall through dependency for branches
                                ts.add_dependency(atomic_block_entry_addr.to_string(), atomic_block_fallthrough_addr.to_string());
                            },
                            _ => (),
                        }
                        atomic_block_entry_addr = atomic_block_fallthrough_addr;
                    } else {
                        panic!("[generate_function_model] jal instruction does not have an immediate value; possibly an invalid objdump.");
                    }
                }
                "jalr" => {
                    ts.add_dependency(atomic_block_entry_addr.to_string(), "");
                }
                _ => (),
            };
        }
        // Generate the procedures for functions recursively
        let mut procedure_body = String::from("");
        while let mut v = ts.pop_all() {
            if v.is_empty() {
                if ts.len() != 0 {
                    debug!(
                        "[generate_function_model] There is a cyclic dependency in the function {}!!!",
                        function_name
                    );
                    return Err(NoSuchModelError{ recursive_function: function_name.to_string() });
                }
                break;
            }
            v.sort();
            // debug!(
            //     "TS: {:?}",
            //     v.iter()
            //         .map(|x| format!("{:#x}", dec_str_to_u64(x).unwrap_or(0xffffffff)))
            //         .collect::<Vec<_>>()
            // );
            for addr in v {
                if let Ok(pc_addr) = dec_str_to_u64(&addr[..]) {
                    let call = &self.call_atomic_block(pc_addr);
                    procedure_body = format!(
                        "{}      if (pc == {}) {{\n{}\n      }}\n",
                        procedure_body,
                        &self.u64_to_uclid_bv_lit(pc_addr),
                        call
                    );
                }
            }
        }
        self.add_uclid_procedure(
            &function_vec[0].function_name().to_string(),
            &procedure_body,
        );
        // TODO: Add this at the top and do a DFS bottom up to get the modifies set
        // Generate the rest
        let absolute_target_addrs = UclidTranslator::absolute_addrs_set(function_vec);
        for addr in absolute_target_addrs {
            if UclidTranslator::is_function_entry_addr(&addr, function_vecs) {
                let function_name = UclidTranslator::function_name_from_addr(&addr, function_vecs);
                match self.generate_function_model_by_entry_addr(&addr, function_vecs, level + 1) {
                    Ok(_) => {
                        debug!(
                            "[generate_function_model_by_entry_addr] Generated a function model for the callee {}.",
                            function_name
                        );
                    },
                    Err(e) => {
                        self.add_uclid_procedure(&UclidTranslator::atomic_block_name(addr), &String::from(""));
                        debug!("[generate_function_model_by_entry_addr] Unable to generate function model for callee {} so a stub function was created.", function_name);
                    },
                }
            }
        }
        Ok(())
    }

    fn function_name_from_addr<'b>(
        address: &u64,
        function_vecs: &'b HashMap<u64, Vec<AssemblyLine>>,
    ) -> &'b str {
        function_vecs.get(address).unwrap()[0].function_name()
    }

    fn function_addr_from_name(
        function_name: &str,
        function_vecs: & HashMap<u64, Vec<AssemblyLine>>,
    ) -> u64 {
        let function_vec = function_vecs
            .values()
            .find(|function_vec| function_vec[0].function_name() == function_name)
            .expect("[generate_function_model] Unable to find function.");
        function_vec[0].address()
    }

    fn is_function_entry_addr(
        address: &u64,
        function_vecs: &HashMap<u64, Vec<AssemblyLine>>,
    ) -> bool {
        function_vecs.get(address).is_some()
    }

    fn call_atomic_block(&self, address: u64) -> String {
        format!(
            "        call {}();",
            UclidTranslator::atomic_block_name(address)
        )
    }

    fn generate_state_variables(&mut self, function_vec: &Vec<AssemblyLine>) {
        let mut variables_xlen_vec = vec![];
        for assembly_line in function_vec {
            if let Some(reg) = assembly_line.rd() {
                variables_xlen_vec.push(reg.to_string());
            }
            if let Some(reg) = assembly_line.rs1() {
                variables_xlen_vec.push(reg.to_string());
            }
            if let Some(reg) = assembly_line.rs2() {
                variables_xlen_vec.push(reg.to_string());
            }
            if let Some(reg) = assembly_line.csr() {
                variables_xlen_vec.push(reg.to_string());
            }
        }
        variables_xlen_vec.sort();
        variables_xlen_vec.dedup();
        for variable in variables_xlen_vec {
            self.add_uclid_state_variable(&variable, &self.uclid_bv_type(self.xlen));
        }
        // Add other system variables
        self.add_uclid_state_variable(&format!("pc"), &self.uclid_bv_type(self.xlen));
        self.add_uclid_state_variable(&format!("mem"), &self.uclid_mem_type());
        self.add_uclid_state_variable(&format!("current_priv"), &self.uclid_bv_type(2));
        self.add_uclid_state_variable(&format!("exception"), &self.uclid_bv_type(self.xlen));
    }

    fn add_uclid_state_variable(&mut self, state_variable_id: &String, type_decl: &String) {
        if self.state_var_ids.get(state_variable_id).is_none() {
            self.state_var_ids.insert(state_variable_id.clone());
            self.state_var_decls
                .push(format!("  var {}: {};\n", state_variable_id, type_decl));
        }
    }

    fn generate_function_atomic_blocks(&mut self, function_vec: &Vec<AssemblyLine>) {
        // debug!(
        //     "{:#?}",
        //     function_vec
        //         .iter()
        //         .map(|line| self.assembly_line_to_uclid(&line))
        //         .collect::<Vec<_>>()
        // );
        // Split function into basic blocks and add them as procedure declaration
        let absolute_addrs = UclidTranslator::absolute_addrs_set(function_vec);
        let mut procedure_body = String::from("");
        let mut block_entry_address: Option<u64> = None;
        for assembly_line in function_vec {
            if block_entry_address.is_none() {
                block_entry_address = Some(assembly_line.address());
            }
            procedure_body = format!(
                "{}\n{}",
                procedure_body,
                self.assembly_line_to_uclid(&assembly_line)
            );
            match assembly_line.base_instruction_name() {
                "beq" | "bne" | "bge" | "blt" | "bltu" | "bgeu" | "jal" | "jalr" => {
                    &self.add_uclid_procedure(
                        &UclidTranslator::atomic_block_name(block_entry_address.unwrap()),
                        &procedure_body,
                    );
                    procedure_body = String::from("");
                    block_entry_address = None;
                }
                _ => {
                    let next_addr = assembly_line.address() + 4;
                    if absolute_addrs.get(&next_addr).is_some() {
                        // End of basic block if the next address is a target address
                        &self.add_uclid_procedure(
                            &UclidTranslator::atomic_block_name(block_entry_address.unwrap()),
                            &procedure_body,
                        );
                        procedure_body = String::from("");
                        block_entry_address = None;
                    }
                }
            }
        }
    }

    fn absolute_addrs_set(assembly_lines: &Vec<AssemblyLine>) -> HashSet<u64> {
        let mut absolute_addrs = HashSet::new();
        for assembly_line in assembly_lines {
            match assembly_line.base_instruction_name() {
                "beq" | "bne" | "bge" | "blt" | "bltu" | "bgeu" | "jal" => {
                    if let InstOperand::Immediate(target_addr) = assembly_line.imm().expect("[generate_function_model] Unable to find a target address for a jump instruction") {
                        absolute_addrs.insert(*target_addr as u64);
                    };
                }
                _ => (),
            }
        }
        absolute_addrs
    }

    fn atomic_block_name(address: u64) -> String {
        format!("atomic_block_{:#x}", address)
    }

    fn add_uclid_procedure(&mut self, name: &String, body: &String) {
        let modifies = format!("    modifies {};", self.state_var_ids.iter().map(|s| s.clone()).collect::<Vec<_>>().join(", "));
        let procedure_decl = format!(
            "  procedure {}() \n{}\n    {{\n{}\n    }}\n\n",
            name, modifies, body
        );
        self.procedures_decls.push(procedure_decl);
    }

    fn assembly_line_to_uclid(&self, assembly_line: &AssemblyLine) -> String {
        let mut outputs = vec![];
        let mut args = vec![];
        if let Some(reg) = assembly_line.csr() {
            outputs.push(reg.to_string());
            args.push(reg.to_string());
        }
        if let Some(reg) = assembly_line.rd() {
            outputs.push(reg.to_string());
        }
        if let Some(reg) = assembly_line.rs1() {
            let offset = assembly_line.offset().unwrap_or(0);
            match offset {
                0 => args.push(format!("{}", reg.to_string())),
                _ => args.push(format!(
                    "{} + {}",
                    reg.to_string(),
                    self.i64_to_uclid_bv_lit(offset)
                )),
            }
        }
        if let Some(reg) = assembly_line.rs2() {
            // split_size is the correct bit size of the value rs2 for calling store instructions
            let split_size = match assembly_line.base_instruction_name() {
                "sb" => "[7:0]",
                "sh" => "[15:0]",
                "sw" => "[31:0]",
                _ => "",
            };
            args.push(format!("{}{}", reg.to_string(), split_size));
        }
        if let Some(imm) = assembly_line.imm() {
            if let InstOperand::Immediate(value) = imm {
                args.push(format!("{}", self.i64_to_uclid_bv_lit(*value as i64)));
            }
        }
        format!(
            "      call ({}) = {}_proc({});",
            outputs.join(", "),
            assembly_line.base_instruction_name(),
            args.join(", ")
        )
    }

    fn i64_to_uclid_bv_lit(&self, dec: i64) -> String {
        format!("{}{}", dec, &self.uclid_bv_type(self.xlen))
    }

    fn u64_to_uclid_bv_lit(&self, dec: u64) -> String {
        format!("{}{}", dec, &self.uclid_bv_type(self.xlen))
    }

    fn uclid_bv_type(&self, len: u64) -> String {
        format!("bv{}", len)
    }

    fn uclid_array_type(&self, index: u64, value: u64) -> String {
        format!(
            "[{}]{}",
            self.uclid_bv_type(index),
            self.uclid_bv_type(value)
        )
    }

    fn uclid_mem_type(&self) -> String {
        // Byte-valued memory with XLEN addresses
        self.uclid_array_type(self.xlen, 8)
    }

    pub fn write_model(&mut self, write_to_filepath: &str) -> std::io::Result<()> {
        let mut writer = File::create(write_to_filepath)?;
        writer.write_all(b"module main {\n")?;
        let prelude = fs::read_to_string("models/prelude.ucl")?;
        writer.write_all(prelude.as_bytes())?;
        writer.write_all(b"\n")?;
        for import_decl in &self.import_decls {
            writer.write_all(import_decl.as_bytes())?;
        }
        writer.write_all(b"\n")?;
        for define_decl in &self.define_decls {
            writer.write_all(define_decl.as_bytes())?;
        }
        writer.write_all(b"\n")?;
        for state_var in &self.state_var_decls {
            writer.write_all(state_var.as_bytes())?;
        }
        writer.write_all(b"\n")?;
        for procedure_decl in &self.procedures_decls {
            writer.write_all(procedure_decl.as_bytes())?;
        }
        writer.write_all(b"\n")?;
        writer.write_all(b"  init {\n")?;
        for init_stmt in &self.init_stmts {
            writer.write_all(init_stmt.as_bytes())?;
        }
        writer.write_all(b"  }\n\n")?;
        writer.write_all(b"  next {\n")?;
        for next_stmt in &self.next_stmts {
            writer.write_all(next_stmt.as_bytes())?;
        }
        writer.write_all(b"  }\n\n")?;
        writer.write_all(b"  control {\n")?;
        for control_stmt in &self.control_stmts {
            writer.write_all(control_stmt.as_bytes())?;
        }
        writer.write_all(b"  }\n")?;
        writer.write_all(b"}\n")?;
        writer.sync_all()?;
        Ok(())
    }
}
