use std::collections::HashMap;
use std::fs;

use crate::spec_lang::sl_ast;
use crate::spec_lang::sl_ast::ASTRewriter;
use crate::spec_lang::sl_lexer;

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
    ) -> Result<HashMap<String, Vec<sl_ast::Spec>>, utils::Error> {
        let mut specs_map = HashMap::new();
        for spec_file_path in spec_file_paths {
            specs_map.extend(self.process_spec_file(spec_file_path)?);
        }
        Ok(specs_map)
    }

    fn process_spec_file(
        &self,
        spec_file_path: &str,
    ) -> Result<HashMap<String, Vec<sl_ast::Spec>>, utils::Error> {
        let specs_str = match fs::read_to_string(spec_file_path) {
            Ok(res) => res,
            Err(e) => panic!("Failed to read spec file: {}. {}", spec_file_path, e),
        };
        Ok(self.parse(&specs_str))
    }

    fn parse(&self, input: &str) -> HashMap<String, Vec<sl_ast::Spec>> {
        let lexer = sl_lexer::Lexer::new(input);
        let fun_specs_vec = FuncSpecsParser::new()
            .parse(input, &self.dwarf_ctx, &mut "".to_string(), lexer)
            .unwrap();
        let mut ret = HashMap::new();
        for mut fun_spec in fun_specs_vec {
            let fname = fun_spec.fname.to_string();
            let specs = &mut fun_spec.specs;
            for spec in specs {
                match spec {
                    sl_ast::Spec::Requires(bexpr) | sl_ast::Spec::Ensures(bexpr) => {
                        self.sl_bexpr_rewrite_passes(bexpr);
                    }
                    _ => (),
                }
            }
            ret.insert(fname, fun_spec.specs);
        }
        ret
    }

    fn sl_bexpr_rewrite_passes(&self, bexpr: &mut sl_ast::BExpr) {
        // Rewrite all quantified variable names
        RenameGlobals::rewrite_bexpr(bexpr, &self.dwarf_ctx);
    }
}

/// AST pass that renames the identifiers for global variables from
/// Identifiers `name` to FuncApp `global_var_name()`.
struct RenameGlobals {}
impl sl_ast::ASTRewriter<DwarfCtx> for RenameGlobals {
    fn rewrite_vexpr_ident(ident: &mut sl_ast::VExpr, context: &DwarfCtx) {
        if sl_ast::VExpr::is_global(ident, context) {
            match ident {
                sl_ast::VExpr::Ident(name, typ) => {
                    *ident = sl_ast::VExpr::FuncApp(
                        format!("global_var_{}", name),
                        vec![],
                        typ.clone());
                }
                _ => panic!("Expected identifier.")
            }
        }
    }
}

