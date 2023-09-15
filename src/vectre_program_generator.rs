use std::{
    collections::{
        HashSet,
        HashMap,
    },
    rc ::Rc,
};

use regex::Regex;

use crate::{
    datastructures::cfg,
    disassembler::disassembler::{
        AssemblyLine,
        Inst
    },
};

use itertools::Itertools;

/// Vectre IR disassembler
pub struct VectreProgramGenerator;

impl VectreProgramGenerator {
    /// Returns a vectre program as a string
    pub fn get_vectre_programs_by_bb(func_names: &HashSet<&str>, bbs: &HashMap<u64, Rc<cfg::BasicBlock<AssemblyLine>>>, name_to_addr_map: &HashMap<String, u64>) -> String {
        let mut res = format!("");

        // iterate over the functions and add them to the vectre IR string
        for func_name in func_names {
            // initialize empty string 
            let mut prog_body = format!("");

            // find the function
            if let Some(addr) = name_to_addr_map.get(func_name.to_owned()) {
                // create a new cfg for this function
                let func_cfg = cfg::Cfg::new(*addr, bbs);

                // iterate over the cfg nodes (atomic blocks) and add them to program body
                for (node_addr, node) in func_cfg.nodes().iter().sorted_by_key(|x| x.0) {
                    let succs_addrs_str = node
                        .exit()
                        .successors()
                        .iter()
                        .map(|s| s.to_string())
                        .collect::<Vec<String>>()
                        .join(", ");
                    prog_body = format!("{}    {} {{\n", prog_body, format!("atomic_block({}, [{}])", node_addr, succs_addrs_str));

                    // print the assembly instructions
                    let body = node.insts()
                                .iter()
                                .map(|inst| format!("        {}: {};", inst.addr(), Self::line_to_vectre_str(inst)))
                                .collect::<Vec<String>>()
                                .join("\n");
                    // for inst in node.insts() {
                    //     prog_body = format!("{}        {}: {};\n", prog_body, inst.addr(), Self::line_to_vectre_str(inst));
                    // }
                    prog_body = format!("{}{}", prog_body, body);

                    // add closing brace
                    prog_body = format!("{}\n    }}\n", prog_body);
                }
            } else {
                panic!("[vectre] Could not find function {}.", func_name);
            }            

            if let Some(addr) = name_to_addr_map.get(func_name.to_owned()) {
                // remove all non alphanumeric with underscores
                let re = Regex::new("[^[:alnum:]]").unwrap();
                let func_name_renamed = re.replace_all(func_name, "_");

                res = format!("{}program {}({}) {{\n{}}}\n", res, func_name_renamed, addr, prog_body);
            } else {
                panic!("[vectre] Could not find function {}.", func_name);
            }
        }

        res
    }

    /// Returns the body of the program as a string encoded in the vectre language
    fn line_to_vectre_str(al: &AssemblyLine) -> String {
        let re = Regex::new("[^[:alnum:]]").unwrap();
        let args = al.ops().iter().map(|inst_op| format!("{}", inst_op)).collect::<Vec<String>>().join(", ");        
        let renamed_op = re.replace_all(al.op(), "_");
        format!("{} {}", renamed_op, args)
    }
}
