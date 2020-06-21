use std::collections::HashMap;
use std::fs;

use crate::spec_lang::{
    sl_ast,
    sl_lexer,
};

use dwarf_ctx::dwarfreader::DwarfCtx;

use crate::riscv_spec_lang::FuncSpecsParser;

use crate::utils; 

pub struct SpecParser<'a> {
    dwarf_ctx: &'a DwarfCtx,
}

impl<'a> SpecParser<'a> {
    pub fn new(dwarf_ctx: &'a DwarfCtx) -> Self {
        SpecParser { dwarf_ctx }
    }

    pub fn process_spec_files(
        &self,
        spec_file_paths: &Vec<&str>,
    ) -> Result<Vec<sl_ast::FuncSpec>, utils::Error> {
        let mut specs_map = vec![];
        for spec_file_path in spec_file_paths {
            specs_map.append(&mut self.process_spec_file(spec_file_path)?);
        }
        Ok(specs_map)
    }

    fn process_spec_file(
        &self,
        spec_file_path: &str,
    ) -> Result<Vec<sl_ast::FuncSpec>, utils::Error> {
        let specs_str = match fs::read_to_string(spec_file_path) {
            Ok(res) => res,
            Err(e) => panic!("Failed to read spec file: {}. {}", spec_file_path, e),
        };
        Ok(self.parse(&specs_str))
    }

    fn parse(&self, input: &str) -> Vec<sl_ast::FuncSpec> {
        let lexer = sl_lexer::Lexer::new(input);
        FuncSpecsParser::new()
            .parse(input, &self.dwarf_ctx, &mut "".to_string(), &mut HashMap::new(), lexer)
            .unwrap()
    }
}

