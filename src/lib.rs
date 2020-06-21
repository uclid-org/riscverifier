use std::collections::HashMap;

use dwarf_ctx::dwarfreader::DwarfCtx;
use asts::spec_lang::{
	sl_ast,
	sl_ast::ASTRewriter,
	sl_parser,
};

/// ====================================================================================================
/// # Specifications

pub fn process_specs(spec_files: &Vec<&str>, dwarf_ctx: &DwarfCtx) -> HashMap<String, Vec<sl_ast::Spec>> {
    // Parse specifications
    let spec_parser = sl_parser::SpecParser::new(dwarf_ctx);
    let fun_specs_vec = spec_parser.process_spec_files(spec_files)
        .expect("Could not read spec.");

    // Run a set of passes over each individual specification expression
    let mut ret = HashMap::new();
    for mut fun_spec in fun_specs_vec {
        let fname = fun_spec.fname.to_string();
        let specs = &mut fun_spec.specs;
        for spec in specs {
            match spec {
                sl_ast::Spec::Requires(bexpr) | sl_ast::Spec::Ensures(bexpr) => {
                    sl_bexpr_rewrite_passes(bexpr, dwarf_ctx);
                }
                _ => (),
            }
        }
        ret.insert(fname, fun_spec.specs);
    }
    ret
}

fn sl_bexpr_rewrite_passes(bexpr: &mut sl_ast::BExpr, dwarf_ctx: &DwarfCtx) {
    // Rewrite all quantified variable names
    RenameGlobals::rewrite_bexpr(bexpr, dwarf_ctx);
}

/// ====================================================================================================
/// ## Specification transformation passes

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

