use std::collections::HashMap;
use std::fs;

use crate::spec_lang::sl_ast;
use crate::spec_lang::sl_lexer;

use crate::readers::dwarfreader::DwarfCtx;
use crate::utils;

pub struct SpecParser<'a> {
    xlen: u64,
    dwarf_ctx: &'a DwarfCtx,
}

impl<'a> SpecParser<'a> {
    pub fn new(xlen: u64, dwarf_ctx: &'a DwarfCtx) -> Self {
        SpecParser { xlen, dwarf_ctx }
    }

    pub fn process_spec_files(
        &self,
        spec_file_paths: &Vec<&str>,
    ) -> Result<HashMap<String, Vec<Box<sl_ast::Spec>>>, utils::Error> {
        let mut specs_map = HashMap::new();
        for spec_file_path in spec_file_paths {
            specs_map.extend(self.process_spec_file(spec_file_path)?);
        }
        Ok(specs_map)
    }

    fn process_spec_file(
        &self,
        spec_file_path: &str,
    ) -> Result<HashMap<String, Vec<Box<sl_ast::Spec>>>, utils::Error> {
        let specs_str = match fs::read_to_string(spec_file_path) {
            Ok(res) => res,
            Err(e) => panic!("Failed to read spec file: {}. {}", spec_file_path, e),
        };
        Ok(self.parse(&specs_str))
    }

    fn parse(&self, input: &str) -> HashMap<String, Vec<Box<sl_ast::Spec>>> {
        let lexer = sl_lexer::Lexer::new(input);
        let fun_specs_vec = crate::riscv_spec_lang::FuncSpecsParser::new()
            .parse(input, lexer)
            .unwrap();
        let mut ret = HashMap::new();
        for fun_spec in fun_specs_vec {
            let fname = fun_spec.fname.clone();
            let specs = fun_spec.specs;
            ret.insert(fname, specs);
        }
        ret
    }
}
