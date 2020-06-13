use crate::readers::dwarfreader::DwarfCtx;

pub struct SpecTemplatePrinter;

impl SpecTemplatePrinter {
	pub fn fun_templates(dwarf_ctx: &DwarfCtx) -> String {
		let mut template = format!("");
		for (fname, func_sig) in dwarf_ctx.func_sigs() {
			let args = func_sig.args.iter().fold(format!(""), |acc, arg| format!("{}, {:?}", acc, arg));
			let ret_type = if let Some(ret_type) = &func_sig.ret_type {
				format!("{:?} ", ret_type)
			} else {
				format!("")
			};
			let signature = format!("{}{}({})", ret_type, fname, args);
			template = format!("{}spec {} {{\n	// {}\n}}\n", template, fname, signature);
		}
		template
	}
}