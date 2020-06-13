use std::collections::HashSet;

use crate::readers::dwarfreader::{DwarfCtx, DwarfTypeDefn, DwarfVar};
use crate::utils;

/// Simple specification template generator
pub struct SpecTemplateGenerator;

impl SpecTemplateGenerator {
    /// Returns a specification template as a string
    pub fn fun_templates(
        func_names: &HashSet<String>,
        dwarf_ctx: &DwarfCtx,
    ) -> Result<String, utils::Error> {
        let mut template = format!("");
        // Iterate over the function signatures and add them to the template
        for fname in func_names.iter() {
            let func_sig = dwarf_ctx.func_sig(fname)?;
            // Create the arguments, return type, and signature strings comments
            let args = &func_sig.args.iter().fold(format!(""), |acc, arg| {
                let arg_str = SpecTemplateGenerator::var_to_string(arg);
                format!("{}, {}", acc, arg_str)
            })[2..];
            let ret_type_str = if let Some(ret_type) = &func_sig.ret_type {
                format!("{} ", SpecTemplateGenerator::type_to_string(ret_type))
            } else {
                format!("")
            };
            let signature = format!("{}{}({})", ret_type_str, fname, args);
            // Add the specification template to the file
            template = format!("{}spec {} {{\n	// {}\n}}\n", template, fname, signature);
        }
        Ok(template)
    }

    /// Returns the string version of the variable
    pub fn var_to_string(var: &DwarfVar) -> String {
        let type_str = SpecTemplateGenerator::type_to_string(&*var.typ_defn);
        format!("{}: {}", var.name, type_str)
    }

    pub fn type_to_string(typ: &DwarfTypeDefn) -> String {
        match typ {
            DwarfTypeDefn::Primitive { bytes } => format!("bv{}", bytes * utils::BYTE_SIZE),
            DwarfTypeDefn::Array {
                in_typ,
                out_typ,
                bytes,
            } => format!("bv{}", bytes * utils::BYTE_SIZE),
            DwarfTypeDefn::Struct { id, fields, bytes } => {
                format!("bv{}", bytes * utils::BYTE_SIZE)
            }
            DwarfTypeDefn::Pointer { value_typ, bytes } => {
                format!("bv{}", bytes * utils::BYTE_SIZE)
            }
        }
    }
}
