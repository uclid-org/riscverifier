use crate::objectdumpreader::{AssemblyLine, InstOperand};

use std::collections::HashMap;

use crate::utils::*;
use std::fs;
use std::fs::File;
use std::io::prelude::*;

pub struct UclidTranslator {
    xlen: u64,
    import_decls: Vec<String>,
    define_decls: Vec<String>,
    state_var_decls: Vec<String>,
    procedures_decls: Vec<String>,
    init_stmts: Vec<String>,
    next_stmts: Vec<String>,
    control_stmts: Vec<String>,
}

impl UclidTranslator {
    pub fn create(xlen: u64) -> UclidTranslator {
        UclidTranslator {
            xlen,
            import_decls: vec![],
            define_decls: vec![],
            state_var_decls: vec![],
            procedures_decls: vec![],
            init_stmts: vec![],
            next_stmts: vec![],
            control_stmts: vec![],
        }
    }

    pub fn reset_model(&mut self) {
        self.import_decls = vec![];
        self.define_decls = vec![];
        self.state_var_decls = vec![];
        self.procedures_decls = vec![];
        self.init_stmts = vec![];
        self.next_stmts = vec![];
        self.control_stmts = vec![];
    }

    pub fn generate_function_model(
        &mut self,
        function_name: &str,
        function_vecs: &HashMap<u64, Vec<AssemblyLine>>,
    ) {
        self.reset_model();
        debug!(
            "[generate_function_model] Generating model for function {}.",
            function_name
        );
        let block = function_vecs
            .values()
            .find(|block| block[0].function_name() == function_name)
            .expect("[generate_function_model] Unable to find function.");
        // debug!("[generate_function_model] {:?}", block.iter().map(|line| line.base_instruction_name()).collect::<Vec<_>>());
        self.generate_state_variables(block);
        self.generate_function_atomic_blocks(block);
        let tmp = vec![];
        let cfg = compute_cfg(&tmp).expect("[generate_function_model] Unable to compute CFG");
        let ordered_addresses = topological_sort(&cfg)
            .expect("[generate_function_model] Unable to topologically sort.");
        // Generate the procedures for functions recursively
        self.generate_function_procedure(block);
    }

    fn generate_state_variables(&mut self, function_vec: &Vec<AssemblyLine>) {
        for assembly_line in function_vec {
            
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
        let mut tmp = String::from("");
        let mut block_entry_address: Option<u64> = None;
        for assembly_line in function_vec {
            if block_entry_address.is_none() {
                block_entry_address = Some(assembly_line.address());
            }
            tmp = format!("{}\n{}", tmp, self.assembly_line_to_uclid(&assembly_line));
            match assembly_line.base_instruction_name() {
                "beq" | "bne" | "bge" | "blt" | "bltu" | "bgeu" | "jal" | "jalr" => {
                    &self.add_uclid_procedure(&UclidTranslator::atomic_block_name(block_entry_address.unwrap()), &tmp);
                    tmp = String::from("");
                    block_entry_address = None;
                }
                _ => ()
            }
        }
        // debug!("Split functions: {:#?}", &self.procedures_decls);

    }

    fn generate_function_procedure(&mut self, function_vec: &Vec<AssemblyLine>) {
        
    }

    fn atomic_block_name(address: u64) -> String {
        format!("atomic_block_{}", address.to_string())
    }

    fn add_uclid_procedure(&mut self, name: &String, body: &String) {
        let procedure_decl = format!("  procedure {} {{\n{}\n  }}\n\n", name, body);
        self.procedures_decls.push(procedure_decl);
    }

    // TODO:
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
                _ => args.push(format!("{} + {}", reg.to_string(), self.dec_to_bv(offset))),
            }
        }
        if let Some(reg) = assembly_line.rs2() {
            args.push(reg.to_string());
        }
        if let Some(imm) = assembly_line.imm() {
            if let InstOperand::Immediate(value)  = imm {
                args.push(format!("{}", self.dec_to_bv(*value)));
            }
        }
        format!(
            "    call ({}) = {}_proc({});",
            outputs.join(", "),
            assembly_line.base_instruction_name(),
            args.join(", ")
        )
    }

    fn dec_to_bv(&self, dec: i64) -> String {
        format!("{}bv{}", dec, self.xlen)
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
        for define_decl in &self.define_decls {
            writer.write_all(define_decl.as_bytes())?;
        }
        for state_var in &self.state_var_decls {
            writer.write_all(state_var.as_bytes())?;
        }
        for procedure_decl in &self.procedures_decls {
            writer.write_all(procedure_decl.as_bytes())?;
        }
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
