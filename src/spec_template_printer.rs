use crate::readers::dwarfreader::DwarfCtx;

/// Simple specification template generator
pub struct SpecTemplatePrinter;

impl SpecTemplatePrinter {
    pub fn fun_templates(dwarf_ctx: &DwarfCtx) -> String {
        let mut template = format!("");
        // Iterate over the function signatures and add them to the template
        for (fname, func_sig) in dwarf_ctx.func_sigs() {
            // Create the arguments, return type, and signature strings comments
            let args = func_sig
                .args
                .iter()
                .fold(format!(""), |acc, arg| format!("{}, {:?}", acc, arg));
            let ret_type = if let Some(ret_type) = &func_sig.ret_type {
                format!("{:?} ", ret_type)
            } else {
                format!("")
            };
            let signature = format!("{}{}({})", ret_type, fname, args);
            // Add the specification template to the file
            template = format!("{}spec {} {{\n	// {}\n}}\n", template, fname, signature);
        }
        template
    }
}
