use std::collections::HashSet;

use dwarf_ctx::dwarfreader::{DwarfCtx, DwarfTypeDefn, DwarfVar};
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
            let func_sig = dwarf_ctx
                .func_sig(fname)
                .expect(&format!("Unable to find dwarf information for {}.", fname));
            // Create the arguments, return type, and signature strings comments
            let func_sig_args_iter = &mut func_sig.args.iter();
            let args_init_str = if let Some(first_arg) = &func_sig_args_iter.next() {
                SpecTemplateGenerator::var_to_string(first_arg)
            } else {
                format!("")
            };
            let args = &func_sig_args_iter.fold(args_init_str, |acc, arg| {
                let arg_str = SpecTemplateGenerator::var_to_string(arg);
                format!("{}, {}", acc, arg_str)
            });
            let ret_type_str = if let Some(ret_type) = &func_sig.ret_type {
                format!("{} ", SpecTemplateGenerator::type_to_string(ret_type))
            } else {
                format!("")
            };
            let signature = format!("{}{}({})", ret_type_str, fname, args);
            // Add the specification template to the file
            template = format!("{}fun {} {{\n	// {}\n}}\n", template, fname, signature);
        }
        Ok(template)
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
            DwarfTypeDefn::Primitive { bytes } => format!("bv{}", bytes * utils::BYTE_SIZE),
            DwarfTypeDefn::Array {
                in_typ:_,
                out_typ:_,
                bytes,
            } => format!("bv{}", bytes * utils::BYTE_SIZE),
            DwarfTypeDefn::Struct { id:_, fields:_, bytes } => {
                format!("bv{}", bytes * utils::BYTE_SIZE)
            }
            DwarfTypeDefn::Pointer { value_typ:_, bytes } => {
                format!("bv{}", bytes * utils::BYTE_SIZE)
            }
        }
    }
}
