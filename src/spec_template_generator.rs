use std::collections::HashSet;

use dwarf_ctx::dwarfreader::{DwarfCtx, DwarfTypeDefn, DwarfVar};

use utils::constants::BYTE_SIZE;

/// Simple specification template generator
pub struct SpecTemplateGenerator;

impl SpecTemplateGenerator {
    /// Returns a specification template as a string
    pub fn fun_templates(func_names: &HashSet<String>, dwarf_ctx: &DwarfCtx) -> String {
        let mut template = format!("");
        // Iterate over the function signatures and add them to the template
        for fname in func_names.iter() {
            // Find the function
            let func_sig_res = dwarf_ctx.func_sig(fname);
            if let Ok(func_sig) = func_sig_res {
                // Create comma separated argument and return type strings
                let args = &func_sig
                    .args
                    .iter()
                    .map(|arg| SpecTemplateGenerator::var_to_string(arg))
                    .collect::<Vec<String>>()
                    .join(",");
                let ret_type_str = &func_sig.ret_type.as_ref().map_or(String::from(""), |rt| {
                    SpecTemplateGenerator::type_to_string(rt)
                });
                // Construct the signature
                let signature = format!("{}{}({})", ret_type_str, fname, args);
                // Add function signature to the specification template string
                template = format!("{}fun {} {{\n	// {}\n}}\n", template, fname, signature);
            } else {
                // Unable to generate template
                let silent_msg = format!("Unable to generate template for {}.", fname);
                template = format!("{}// {}", fname, silent_msg);
            }
        }
        template
    }

    /// Returns the string representation of the variable
    /// Used for comments in specification templates
    pub fn var_to_string(var: &DwarfVar) -> String {
        let type_str = SpecTemplateGenerator::type_to_string(&*var.typ_defn);
        format!("{}: {}", var.name, type_str)
    }

    /// Returns the string represention of the type
    /// Used for comments in specification templates
    pub fn type_to_string(typ: &DwarfTypeDefn) -> String {
        match typ {
            DwarfTypeDefn::Primitive { bytes } => format!("bv{}", bytes * BYTE_SIZE),
            DwarfTypeDefn::Array {
                in_typ: _,
                out_typ: _,
                bytes,
            } => format!("bv{}", bytes * BYTE_SIZE),
            DwarfTypeDefn::Struct {
                id: _,
                fields: _,
                bytes,
            } => format!("bv{}", bytes * BYTE_SIZE),
            DwarfTypeDefn::Pointer {
                value_typ: _,
                bytes,
            } => format!("bv{}", bytes * BYTE_SIZE),
        }
    }
}
