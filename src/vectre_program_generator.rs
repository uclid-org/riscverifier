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
    disassembler::disassembler::AssemblyLine,
};


/// Simple specification template generator
pub struct VectreProgramGenerator;

impl VectreProgramGenerator {
    /// Returns a vectre program as a string
    pub fn get_vectre_programs(func_names: &HashSet<&str>, als: &Vec<Rc<AssemblyLine>>) -> String {
        if als.is_empty() {
            return "".to_string();
        }

        // Result string of vectre programs to return
        let mut res = format!("");

        let mut curr_func_name = &als[0].function_name()[..];
        let mut body = "".to_string();

        for al in als {
            let al_func_name = &al.function_name()[..];
            
            // skip function if it's not listed
            if !func_names.contains(al_func_name) {
                continue;
            }

            // new function seen, add the previous one to the result string
            if al_func_name != curr_func_name {
                // add previous function
                if body.len() != 0 {
                    res = format!("{}prog {} {{\n{}}}\n\n", res, curr_func_name, body);
                    body = "".to_string();
                }

                // set this as a new function
                curr_func_name = al_func_name;
            }

            // add the current instruction to the program
            body = format!("{}    {}: {};\n", body, al.addr(), Self::line_to_vectre_str(&*al));
        }

        // add the last function
        if body.len() != 0 && func_names.contains(curr_func_name) {
            res = format!("{}prog {} {{\n{}}}\n\n", res, curr_func_name, body);
        }

        res
    }

    /// Returns a vectre program as a string
    pub fn get_vectre_programs_by_bb(func_names: &HashSet<&str>, bbs: &HashMap<u64, Rc<cfg::BasicBlock<AssemblyLine>>>, name_to_addr_map: &HashMap<String, u64>) -> String {
        let mut res = format!("");

        // Iterate over the programs to print
        for func_name in func_names {
            // Find the function
            let mut prog_body = format!("");
            if let Some(addr) = name_to_addr_map.get(func_name.to_owned()) {
                // create a new cfg for this function
                let func_cfg = cfg::Cfg::new(*addr, bbs);

                // iterate over the cfg nodes and add them to program body
                for (node_addr, node) in func_cfg.nodes() {
                    prog_body = format!("{}{}:\n", prog_body, format!("ENTRY_{}", node_addr));
                    // print the instructions
                    for inst in node.insts() {
                        prog_body = format!("{}    {}: {};\n", prog_body, inst.addr(), Self::line_to_vectre_str(inst));
                    }
                }
            } else {
                panic!("[vectre] Could not find function {}.", func_name);
            }
            
            // remove all non alphanumeric with underscores
            let re = Regex::new("[^[:alnum:]]").unwrap();
            let func_name_renamed = re.replace_all(func_name, "_");

            res = format!("{}prog {} {{\n{}\n}}\n", res, func_name_renamed, prog_body);
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
