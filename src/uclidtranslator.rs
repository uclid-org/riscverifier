use std::collections::{HashMap, HashSet};
use std::fs;
use std::fs::File;
use std::io::prelude::*;

use topological_sort::TopologicalSort;

use crate::objectdumpreader::{AssemblyLine, InstOperand};

use crate::utils::*;

use crate::dwarfreader::{DwarfReader, FunctionSig};

const JUMP_INSTS: &'static [&'static str] = &["jal", "jalr"];
const BRANCH_INSTS: &'static [&'static str] = &["beq", "bne", "blt", "bge", "bltu", "bgeu"];
const BYTE_SIZE: &'static u64 = &8;

pub struct UclidTranslator<'a> {
    xlen: u64,
    inst_length: u64,
    dwarf_reader: &'a DwarfReader,
    function_vecs: &'a HashMap<u64, Vec<AssemblyLine>>,
    ignored_functions: &'a HashSet<&'a str>,
    generated_functions: HashSet<String>,
    import_decls: Vec<String>,
    define_decls: Vec<String>,
    state_var_decls: Vec<String>,
    const_var_decls: Vec<String>,
    identifiers: HashSet<String>,
    procedures_decls: Vec<String>,
    function_signatures: HashMap<String, FunctionSig>,
    axiom_decls: Vec<String>,
    init_stmts: Vec<String>,
    next_stmts: Vec<String>,
    control_stmts: Vec<String>,
    modifies_set_map: HashMap<u64, HashSet<String>>,
}

impl<'a> UclidTranslator<'a> {
    pub fn create(
        xlen: u64,
        dwarf_reader: &'a DwarfReader,
        ignored_functions: &'a HashSet<&'a str>,
        function_vecs: &'a HashMap<u64, Vec<AssemblyLine>>,
    ) -> UclidTranslator<'a> {
        UclidTranslator {
            xlen,
            inst_length: 4,
            dwarf_reader,
            function_vecs,
            ignored_functions,
            generated_functions: HashSet::new(),
            import_decls: vec![],
            define_decls: vec![],
            state_var_decls: vec![],
            const_var_decls: vec![],
            identifiers: HashSet::new(),
            procedures_decls: vec![],
            function_signatures: HashMap::new(),
            axiom_decls: vec![],
            init_stmts: vec![],
            next_stmts: vec![],
            control_stmts: vec![],
            modifies_set_map: HashMap::new(),
        }
    }

    pub fn reset_model(&mut self) {
        self.generated_functions = HashSet::new();
        self.import_decls = vec![];
        self.define_decls = vec![];
        self.state_var_decls = vec![];
        self.const_var_decls = vec![];
        self.identifiers = HashSet::new();
        self.procedures_decls = vec![];
        self.function_signatures = HashMap::new();
        self.axiom_decls = vec![];
        self.init_stmts = vec![];
        self.next_stmts = vec![];
        self.control_stmts = vec![];
        self.modifies_set_map = HashMap::new();
    }

    pub fn generate_function_model(&mut self, function_name: &str) -> Result<(), NoSuchModelError> {
        let function_entry_addr = self.function_addr_from_name(function_name);
        self.generate_function_model_by_entry_addr(&function_entry_addr, 0)?;
        // Generate ignored functions
        for function_name in self.ignored_functions.iter() {
            let function_entry_addr = self.function_addr_from_name(function_name);
            self.add_uclid_procedure(
                &function_entry_addr,
                &HashSet::new(),
                &String::from(""),
                true,
                false,
            )
        }
        Ok(())
    }

    fn generate_function_model_by_entry_addr(
        &mut self,
        function_addr: &u64,
        level: usize,
    ) -> Result<(), NoSuchModelError> {
        let function_name = self.function_name_from_addr(function_addr);
        if self.ignored_functions.get(&function_name).is_some() {
            debug!(
                "[generate_function_model_by_entry_addr] Ignored function {}.",
                function_name
            );
            return Err(NoSuchModelError {
                recursive_function: function_name.to_string(),
            });
        }
        if self.generated_functions.contains(function_name) {
            debug!(
                "[generate_function_model] Cyclic function call for function or already generated {}.",
                function_name
            );
            return Err(NoSuchModelError {
                recursive_function: function_name.to_string(),
            });
        }
        // Vector of assembly lines in the function
        let function_vec = self
            .function_vecs
            .get(function_addr)
            .expect("[generate_function_model_by_entry_addr] Invalid function entry address.");
        // Generate state variables
        self.generate_state_variables(function_vec);
        // Generate the callee functions DFS
        let mut modifies_set = HashSet::new();
        let absolute_target_addrs = UclidTranslator::absolute_addrs_set(function_vec);
        for addr in absolute_target_addrs {
            if self.is_function_entry_addr(&addr) {
                let function_name = self.function_name_from_addr(&addr);
                match self.generate_function_model_by_entry_addr(&addr, level + 1) {
                    Ok(_) => {
                        debug!(
                            "[generate_function_model_by_entry_addr] Generated a function model for the callee {}.",
                            function_name
                        );
                        modifies_set = modifies_set.union(
                            &self
                                .modifies_set_map
                                .get(&addr)
                                .unwrap_or_else(|| panic!(
                                    "[generate_function_model_by_entry_addr] Missing modifies set for {}.",
                                    function_name
                                    )
                                ),
                        ).map(|s| s.clone()).collect::<HashSet<String>>();
                    }
                    Err(e) => (),
                }
            } else {
                // Check if it's a cross function basic block call
                if function_vec
                    .iter()
                    .find(|line| line.address() == addr)
                    .is_none()
                {
                    panic!("[generate_function_model_by_entry_addr] Cross function basic block calls not supported! Occured in function {} at address {:#x}", function_name, addr);
                }
            }
        }
        debug!(
            "[generate_function_model_by_entry_addr] Trying to generate...{}{}",
            format!("{:.<1$}", "", level * 2),
            function_vec[0].function_name()
        );
        // Generate the basic blocks for each function
        let atomic_blocks_modifies_set = self.generate_function_atomic_blocks(function_vec);
        modifies_set = modifies_set
            .union(&atomic_blocks_modifies_set)
            .map(|s| s.clone())
            .collect::<HashSet<String>>();
        // Compute the CFG and topologically sort it to construct function procedure
        let mut ts = TopologicalSort::<String>::new();
        let mut atomic_block_entry_addr: u64 = function_vec[0].address();
        // Stores a map from basic block to callees
        let mut call_map: HashMap<u64, (u64, u64)> = HashMap::new();
        for assembly_line in function_vec {
            let atomic_block_fallthrough_addr = assembly_line.address() + self.inst_length;
            match assembly_line.base_instruction_name() {
                "jal" | "beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu" => {
                    if let InstOperand::Immediate(atomic_block_jump_addr) = assembly_line.imm().expect("[generate_function_model] Unable to find a target address for a jump instruction") {
                        match assembly_line.base_instruction_name() {
                            "beq" | "bne" | "blt" | "bge" | "bltu" | "bgeu"  => {
                                // Add default fall through dependency for branches
                                ts.add_dependency(atomic_block_entry_addr.to_string(), atomic_block_fallthrough_addr.to_string());
                            },
                            "jal" => {
                                if self.is_function_entry_addr(&(*atomic_block_jump_addr as u64)) && *atomic_block_jump_addr as u64 != *function_addr {
                                    // Add jump to another function, which will return (unless interrupted but we aren't dealing with those yet) 
                                    ts.add_dependency(atomic_block_entry_addr.to_string(), atomic_block_fallthrough_addr.to_string());
                                    call_map.insert(atomic_block_entry_addr, (*atomic_block_jump_addr as u64, atomic_block_fallthrough_addr));
                                } else {
                                    // Jump to another block
                                    ts.add_dependency(atomic_block_entry_addr.to_string(), atomic_block_jump_addr.to_string());
                                }
                            },
                            _ => panic!("[generate_function_model_by_entry_addr] Not a jump instruction."),
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
                // If ts.pop_all() is empty and len() != 0, then there is a cycle (from the documentation of topological sort)
                if ts.len() != 0 {
                    debug!(
                        "[generate_function_model] There is a cyclic dependency in the function {}!!!",
                        function_name
                    );
                    return Err(NoSuchModelError {
                        recursive_function: function_name.to_string(),
                    });
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
                if let Ok(u64_addr) = dec_str_to_u64(&addr[..]) {
                    procedure_body = format!(
                        "{}      if (pc == {}) {{\n{}\n      }}\n",
                        procedure_body,
                        &self.u64_to_uclid_bv_lit(u64_addr),
                        self.call_atomic_block(u64_addr)
                    );
                    if call_map.get(&u64_addr).is_some() {
                        let absolute_jump_addr = call_map.get(&u64_addr).unwrap().0;
                        let callee_name = self.function_name_from_addr(&absolute_jump_addr);
                        let fallthrough_addr = call_map.get(&u64_addr).unwrap().1;
                        let function_signature = if !self.ignored_functions.contains(callee_name) {
                            self.function_signatures.get(callee_name)
                        } else {
                            None
                        };
                        let callee_arguments = if let Some(signature) = function_signature {
                            signature.in_types
                            .iter()
                            .enumerate()
                            .map(|(index, name_size_pair)| {
                                if index > 7 {
                                    panic!("[generate_function_model_by_entry_addr] Currently not supporting more than 8 arguments.");
                                }
                                format!("a{}[{}:0]", index, name_size_pair.1 * (*BYTE_SIZE) - 1)
                            }).collect::<Vec<String>>().join(", ")
                        } else {
                            "".to_string()
                        };
                        procedure_body = format!(
                            "{}      assert(pc == {});\n{}\n      assert(pc == {});\n",
                            procedure_body,
                            self.u64_to_uclid_bv_lit(absolute_jump_addr),
                            format!("      call () = {}({});", callee_name, callee_arguments),
                            self.u64_to_uclid_bv_lit(fallthrough_addr),
                        );
                        if !self.ignored_functions.contains(callee_name) {
                            modifies_set = modifies_set
                                .union(&self.modifies_set_map.get(&absolute_jump_addr).unwrap_or_else(|| {
                                        panic!("[generate_function_model_by_entry_addr] Missing modifies set for function {}.", callee_name);
                                }))
                                .map(|s| s.clone())
                                .collect::<HashSet<String>>();
                        }
                    }
                }
            }
        }
        self.add_uclid_procedure(&function_addr, &modifies_set, &procedure_body, false, false);
        // Update modifies set for this function
        self.modifies_set_map.insert(*function_addr, modifies_set);
        Ok(())
    }

    fn function_name_from_addr(&self, address: &u64) -> &'a str {
        self.function_vecs.get(address).unwrap()[0].function_name()
    }

    fn function_addr_from_name(&self, function_name: &str) -> u64 {
        let function_vec = self
            .function_vecs
            .values()
            .find(|function_vec| function_vec[0].function_name() == function_name)
            .expect("[generate_function_model] Unable to find function.");
        function_vec[0].address()
    }

    fn is_function_entry_addr(&self, address: &u64) -> bool {
        self.function_vecs.get(address).is_some()
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
        self.add_uclid_const_variable(
            &format!("zero_const"),
            &self.uclid_bv_type(self.xlen),
            Some(format!("0bv{}", self.xlen)),
        );
    }

    fn add_uclid_state_variable(&mut self, state_variable_id: &String, type_decl: &String) {
        if self.identifiers.get(state_variable_id).is_none() {
            self.identifiers.insert(state_variable_id.clone());
            self.state_var_decls
                .push(format!("  var {}: {};\n", state_variable_id, type_decl));
        }
    }

    fn add_uclid_const_variable(
        &mut self,
        const_variable_id: &String,
        type_decl: &String,
        init_value: Option<String>,
    ) {
        if self.identifiers.get(const_variable_id).is_none() {
            self.identifiers.insert(const_variable_id.clone());
            self.const_var_decls
                .push(format!("  const {}: {};\n", const_variable_id, type_decl));
            if let Some(value) = init_value {
                self.axiom_decls
                    .push(format!("  axiom({} == {});\n", const_variable_id, value));
            }
        }
    }

    fn generate_function_atomic_blocks(
        &mut self,
        function_vec: &Vec<AssemblyLine>,
    ) -> HashSet<String> {
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
        let mut function_modifies_set = HashSet::new();
        let mut atomic_block_modifies_set = HashSet::new();
        for assembly_line in function_vec {
            // Initialize new block entry address
            if block_entry_address.is_none() {
                block_entry_address = Some(assembly_line.address());
            }
            // Update modifies set and add to procedure body
            let (assembly_line_function_modifies_set, next_uclid_assembly_line) =
                self.assembly_line_to_uclid(&assembly_line);
            atomic_block_modifies_set = atomic_block_modifies_set
                .union(&assembly_line_function_modifies_set)
                .map(|s| s.clone())
                .collect::<HashSet<String>>();;
            procedure_body = format!("{}\n{}", procedure_body, next_uclid_assembly_line,);
            // Add to procedure declarations if it's the end of a atomic block
            let next_addr = assembly_line.address() + 4;
            let base_instruction_name = assembly_line.base_instruction_name();
            if JUMP_INSTS
                .iter()
                .find(|s| **s == base_instruction_name)
                .is_some()
                || BRANCH_INSTS
                    .iter()
                    .find(|s| **s == base_instruction_name)
                    .is_some()
                || absolute_addrs.get(&next_addr).is_some()
            {
                // Add the atomic block procedure
                &self.add_uclid_procedure(
                    &block_entry_address.unwrap(),
                    &atomic_block_modifies_set,
                    &procedure_body,
                    true,
                    true,
                );
                function_modifies_set = function_modifies_set
                    .union(&atomic_block_modifies_set)
                    .map(|s| s.clone())
                    .collect::<HashSet<String>>();
                procedure_body = String::from("");
                block_entry_address = None;
                atomic_block_modifies_set = HashSet::new();
            }
        }
        debug!("function mod set: {:?}", function_modifies_set);
        function_modifies_set
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

    fn add_uclid_procedure(
        &mut self,
        entry_addr: &u64,
        modifies_set: &HashSet<String>,
        body: &String,
        inline: bool,
        is_atomic_block: bool,
    ) {
        let function_name = if self.is_function_entry_addr(entry_addr) && !is_atomic_block {
            self.function_name_from_addr(entry_addr).to_string()
        } else {
            UclidTranslator::atomic_block_name(*entry_addr)
        };
        if self.generated_functions.contains(&function_name) {
            debug!("Already added {}.", function_name);
            return;
        } else {
            self.generated_functions.insert(function_name.to_string());
        }
        let (procedure_signature, signature_constraints) = if self
            .is_function_entry_addr(entry_addr)
            && !is_atomic_block
            && !self.ignored_functions.contains(&function_name[..])
        {
            // FIXME: Make one pass instead of many
            let function_signature = self.dwarf_reader.get_function_signature(&function_name);
            // let function_signature = FunctionSig {
            //     in_types: vec![],
            //     out_type: 0,
            // };
            debug!(
                "[add_uclid_procedure] Formals for function {}: {:?}",
                function_name, function_signature
            );
            self.function_signatures
                .insert(function_name.clone(), function_signature.clone());
            (
                format!(
                    "{}",
                    function_signature
                        .in_types
                        .iter()
                        .map(|(formal_name, byte_size)| format!(
                            "{}: {}",
                            formal_name,
                            self.uclid_bv_type((*byte_size * (*BYTE_SIZE)))
                        ))
                        .collect::<Vec<String>>()
                        .join(", ")
                ),
                format!(
                    "    requires {};",
                    function_signature
                        .in_types
                        .iter()
                        .enumerate()
                        .map(|(index, name_size_pair)| {
                            if index > 7 {
                                panic!("[add_uclid_procedure] Currently not supporting arguments with more than 8 arguments.");
                            }
                            format!(
                                "(a{}[{}:0] == {})",
                                index,
                                (name_size_pair.1 * (*BYTE_SIZE) - 1),
                                name_size_pair.0
                            )
                        })
                        .collect::<Vec<String>>()
                        .join(" && ")
                )
            )
        } else {
            ("".to_string(), "".to_string())
        };
        let modifies_string = format!(
            "    modifies {};",
            modifies_set
                .iter()
                .map(|s| s.clone())
                .collect::<Vec<_>>()
                .join(", ")
        );
        let procedure_decl = format!(
            "  procedure {} {}({}) \n{}\n{}\n    {{\n{}\n    }}\n\n",
            if inline { "[inline]" } else { "" },
            function_name,
            procedure_signature,
            if modifies_set.len() > 0 {
                modifies_string
            } else {
                "".to_string()
            },
            signature_constraints,
            body
        );
        self.procedures_decls.push(procedure_decl);
    }

    fn assembly_line_to_uclid(&self, assembly_line: &AssemblyLine) -> (HashSet<String>, String) {
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
        args = args
            .iter()
            .map(|arg| {
                if arg == "zero" {
                    "zero_const".to_string()
                } else {
                    arg.clone()
                }
            })
            .collect::<Vec<_>>();
        if let Some(reg) = assembly_line.rs2() {
            // split_size is the size of the value being stored into memory (refer to models/prelude.ucl)
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
        let uclid_assembly_line_call = format!(
            "      call ({}) = {}_proc({});",
            outputs.join(", "),
            assembly_line.base_instruction_name(),
            args.join(", ")
        );
        let mut modified_vars = match assembly_line.base_instruction_name() {
            "sb" | "sh" | "sw" | "sd" => vec!["pc".to_string(), "mem".to_string()],
            "slli" | "srli" | "csrrwi" | "csrrsi" | "csrrci" | "csrrw" | "csrrs" | "csrrc" => {
                vec!["pc".to_string(), "exception".to_string()]
            }
            _ => vec!["pc".to_string()],
        };
        modified_vars.append(&mut outputs);
        let modifies_set = modified_vars
            .iter()
            .map(|v| v.clone())
            .collect::<HashSet<String>>();
        (modifies_set, uclid_assembly_line_call)
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
        self.uclid_array_type(self.xlen, *BYTE_SIZE)
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
        for const_var in &self.const_var_decls {
            writer.write_all(const_var.as_bytes())?;
        }
        writer.write_all(b"\n")?;
        for procedure_decl in &self.procedures_decls {
            writer.write_all(procedure_decl.as_bytes())?;
        }
        writer.write_all(b"\n")?;
        for axiom in &self.axiom_decls {
            writer.write_all(axiom.as_bytes())?;
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
