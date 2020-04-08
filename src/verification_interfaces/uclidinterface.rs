use std::collections::HashSet;
use std::fs;
use std::rc::Rc;

use crate::ir::*;
use crate::readers::dwarfreader::{DwarfCtx, DwarfTypeDefn, DwarfVar};
use crate::system_model;
use crate::utils;

#[derive(Debug)]
pub struct Uclid5Interface;

impl Uclid5Interface {
    /// Returns a string of the variable declarations in the model
    ///
    /// # Arguments
    ///
    /// * `model` - The model to generate the declarations string for
    fn gen_var_defns(model: &Model) -> String {
        let mut sorted = model.vars.iter().collect::<Vec<_>>();
        sorted.sort();
        let defns = sorted
            .iter()
            .map(|v| format!("var {};", Self::var_decl(v)))
            .collect::<Vec<String>>()
            .join("\n");
        format!("// RISC-V system state variables\n{}", defns)
    }
    /// Reads the model for the RISC-V instructions (provided by utils::PRELUDE_PATH) and returns it as a string
    fn prelude() -> String {
        fs::read_to_string(utils::PRELUDE_PATH).expect("Unable to read prelude.")
    }
    /// Generate a define macro string for each type of array variable
    /// that is a global variable or function argument
    ///
    /// # Arguments
    ///
    /// * `dwarf_ctx` - The DWARF information that contains all the global variables and function
    ///                 signatures for the binaries provided
    fn gen_array_defns(dwarf_ctx: &DwarfCtx) -> String {
        let mut defns: Vec<String> = vec![];
        for var in dwarf_ctx.global_vars() {
            defns.append(&mut Self::gen_array_defn(&var.typ_defn));
        }
        for (_, func_sig) in dwarf_ctx.func_sigs() {
            for var in &func_sig.args {
                defns.append(&mut Self::gen_array_defn(&var.typ_defn));
            }
            if let Some(ret_typ) = &func_sig.ret_typ_defn {
                defns.append(&mut Self::gen_array_defn(&ret_typ));
            }
        }
        defns.sort();
        defns.dedup();
        utils::indent_text(format!("// Array helpers\n{}", defns.join("\n")), 4)
    }
    /// Recursively generate define macros for a given type (size in bytes).
    /// The macro is a function that takes a base address and index
    /// and returns 'base + index * typ_defn.bytes'.
    /// Returns a string representations of these define macros.
    ///
    /// # Arguments
    ///
    /// * `typ_defn` - Type to generate an array index macro for
    ///
    /// # Example
    ///
    /// define index_by_16(base: xlen_t, index: xlen_t): xlen_t = base + bv_left_shift(to_xlen_t(4bv64), index);
    fn gen_array_defn(typ_defn: &DwarfTypeDefn) -> Vec<String> {
        let mut defns = vec![];
        match &typ_defn {
            DwarfTypeDefn::Primitive { bytes } => {
                // Check if the type is valid (bytes > 0)
                if *bytes > 0 {
                    defns.push(format!(
                        "define {}(base: xlen_t, index: xlen_t): xlen_t = base + {};",
                        Self::array_index_macro_name(bytes),
                        Self::multiply_expr(bytes, "index")
                    ))
                }
            }
            DwarfTypeDefn::Array {
                in_typ,
                out_typ,
                bytes: _,
            } => {
                defns.append(&mut Self::gen_array_defn(in_typ));
                defns.append(&mut Self::gen_array_defn(out_typ));
            }
            DwarfTypeDefn::Struct {
                id: _,
                fields,
                bytes,
            } => {
                for (_, field) in fields {
                    defns.append(&mut Self::gen_array_defn(&field.typ));
                }
                if *bytes > 0 {
                    defns.push(format!(
                        "define {}(base: xlen_t, index: xlen_t): xlen_t = base + {};",
                        Self::array_index_macro_name(bytes),
                        Self::multiply_expr(bytes, "index")
                    ))
                }
            }
            DwarfTypeDefn::Pointer {
                value_typ,
                bytes: _,
            } => defns.append(&mut Self::gen_array_defn(&value_typ)),
        };
        defns
    }
    /// Returns the name of the array index macro given the byte size
    fn array_index_macro_name(bytes: &u64) -> String {
        format!("index_by_{}", bytes)
    }
    /// Creates an expression that represents 'num_const * expr'
    /// TODO: Does SMT support precise multiplication? Maybe we can take this out
    fn multiply_expr(num_const: &u64, expr: &str) -> String {
        format!("{:b}", num_const) // Binary expression
            .chars()
            .rev()
            .fold((String::from(""), 0), |acc, x| {
                // acc = (expression, i-th bit counter)
                if x == '1' {
                    (
                        // Add multiple of 2 of the expression to the current expression
                        format!(
                            "bv_left_shift({}, {}){}{}",
                            format!("to_xlen_t({}bv64)", acc.1),
                            expr,
                            if acc.0.len() == 0 { "" } else { " + " },
                            acc.0
                        ),
                        // Increment the i-th bit counter
                        acc.1 + 1,
                    )
                } else {
                    (acc.0, acc.1 + 1)
                }
            })
            .0
    }
    /// Return a string of get field macros for all the type definitions in the global variables
    /// and formal arguments of functions.
    ///  
    /// # Arguments
    ///
    /// * `dwarf_ctx` - The DWARF context containing the variables and function signatures.
    fn gen_struct_defns(dwarf_ctx: &DwarfCtx) -> String {
        let mut defns = vec![];
        for var in dwarf_ctx.global_vars() {
            defns.append(&mut Self::gen_struct_defn(&var.typ_defn));
        }
        for (_, func_sig) in dwarf_ctx.func_sigs() {
            for var in &func_sig.args {
                defns.append(&mut Self::gen_struct_defn(&var.typ_defn));
            }
            if let Some(ret_typ) = &func_sig.ret_typ_defn {
                defns.append(&mut Self::gen_struct_defn(&ret_typ));
            }
        }
        defns.sort();
        defns.dedup();
        utils::indent_text(format!("// Struct helpers\n{}", defns.join("\n")), 4)
    }
    /// Recursively generate string representations of get field macros for type definition 'typ'.
    ///
    /// # Example
    ///
    ///     Given the following struct definition:
    ///     struct ctx { ..., a0: T, ... };
    ///
    ///     This function returns the following definition to simplify 'c.a0', where c is of type ctx:
    ///     define ctx_a0(ptr: xlen_t): xlen_t = ptr + to_xlen_t(80bv64);
    fn gen_struct_defn(typ: &DwarfTypeDefn) -> Vec<String> {
        let mut defns = vec![];
        match typ {
            DwarfTypeDefn::Struct {
                id,
                fields,
                bytes: _,
            } => {
                for (field_name, field) in fields {
                    defns.append(&mut Self::gen_struct_defn(&*field.typ));
                    defns.push(format!(
                        "define {}(ptr: xlen_t): xlen_t = ptr + to_xlen_t({}bv64);",
                        Self::get_field_macro_name(&id[..], field_name),
                        field.loc
                    ));
                }
            }
            DwarfTypeDefn::Array {
                in_typ,
                out_typ,
                bytes: _,
            } => {
                defns.append(&mut Self::gen_struct_defn(&in_typ));
                defns.append(&mut Self::gen_struct_defn(&out_typ));
            }
            _ => (),
        }
        defns
    }
    /// Given the `struct_id` and `field_name`, return the get field macro name.
    fn get_field_macro_name(struct_id: &str, field_name: &String) -> String {
        format!("{}_{}", struct_id, field_name)
    }
    /// Given the dwarf_ctx, returns a string of global variable definitions.
    fn gen_global_defns(dwarf_ctx: &DwarfCtx) -> String {
        let mut defns = String::from("// Global variables\n");
        for var in dwarf_ctx.global_vars() {
            defns = format!("{}{}\n", defns, Self::gen_global_defn(&var));
        }
        utils::indent_text(defns, 4)
    }
    /// Given a global variable, returns a string of a macro that refers to the static
    /// memory location of the variable.
    fn gen_global_defn(global_var: &DwarfVar) -> String {
        format!(
            "define {}(): xlen_t = {};",
            utils::global_var_ptr_name(&global_var.name[..]),
            format!("to_xlen_t({}bv64)", global_var.memory_addr)
        )
    }
    /// Returns a string of macros to refer to a static function's entry address.
    fn gen_global_func_defns(model: &Model) -> String {
        let mut defns = String::from("// Global function entry addresses\n");
        for fm in &model.func_models {
            defns = format!(
                "{}{}\n",
                defns,
                Self::gen_global_func_defn(&fm.sig.name, fm.sig.entry_addr)
            );
        }
        utils::indent_text(defns, 4)
    }
    /// Returns a define macro that returns the `func_entry_addr`
    fn gen_global_func_defn(func_name: &str, func_entry_addr: u64) -> String {
        format!(
            "define {}(): xlen_t = {};",
            utils::global_func_addr_name(func_name),
            format!("to_xlen_t({}bv64)", func_entry_addr)
        )
    }
    /// Returns a string of all the procedures in the model.
    /// This contains all of the function models.
    fn gen_procs(model: &Model, dwarf_ctx: &DwarfCtx) -> String {
        let procs_string = model
            .func_models
            .iter()
            .map(|fm| Self::func_model_to_string(fm, dwarf_ctx))
            .collect::<Vec<_>>()
            .join("\n\n");
        utils::indent_text(procs_string, 4)
    }
    /// Returns the control block for the UCLID5 model.
    /// This currently will automatically verify all functions with
    /// a specification.
    fn control_blk(model: &Model, dwarf_ctx: &DwarfCtx, ignored_funcs: &HashSet<&str>) -> String {
        let verif_fns_string = model
            .func_models
            .iter()
            .filter(|fm| dwarf_ctx.func_sig(&fm.sig.name).is_ok())
            .map(|fm| {
                if !ignored_funcs.contains(&fm.sig.name[..]) {
                    format!(
                        "f{} = verify({});",
                        fm.sig.name.clone(),
                        fm.sig.name.clone()
                    )
                } else {
                    String::from("")
                }
            })
            .collect::<Vec<_>>()
            .join("\n");
        let verif_fns_string = format!("{}\ncheck;\nprint_results;", verif_fns_string);
        let verif_fns_string = utils::indent_text(verif_fns_string, 4);
        let solver_opts = utils::indent_text(format!("set_solver_option(\":mbqi\", false);\nset_solver_option(\":case_split\", 0);\nset_solver_option(\":relevancy\", 0);\nset_solver_option(\":threads\", 4);\nset_solver_option(\":blast_full\", true);"), 4);
        let control_string = format!("control {{\n{}\n{}\n}}", verif_fns_string, solver_opts);
        utils::indent_text(control_string, 4)
    }

    /// =================== Helper functions ===================

    /// Return a UCLID5 variable declaration.
    ///
    /// # Example
    ///
    /// Var = { name: "x".to_string(), typ: Type::Bv { bytes: 64 } } will return:
    /// `x: bv64`
    fn var_decl(var: &Var) -> String {
        format!(
            "{}: {}",
            Self::var_to_string(var),
            Self::typ_to_string(&var.typ)
        )
    }

    /// UCLID5 string that zero extends an expression's bit width.
    fn extend_to_match_width(expr: &str, from: u64, to: u64) -> String {
        if to > from {
            format!("bv_zero_extend({}, {})", to - from, expr)
        } else {
            expr.to_string()
        }
    }
}

impl IRInterface for Uclid5Interface {
    /// IR translation functions
    fn lit_to_string(lit: &Literal) -> String {
        match lit {
            Literal::Bv { val, width } => format!("{}bv{}", *val as i64, width),
            Literal::Bool { val } => format!("{}", val),
        }
    }
    fn typ_to_string(typ: &Type) -> String {
        match typ {
            Type::Unknown => panic!("Type is unknown!"),
            Type::Bool => format!("boolean"),
            Type::Bv { w } => format!("bv{}", w),
            Type::Array { in_typs, out_typ } => format!(
                "[{}]{}",
                in_typs
                    .iter()
                    .map(|typ| Self::typ_to_string(typ))
                    .collect::<Vec<_>>()
                    .join(", "),
                Self::typ_to_string(out_typ)
            ),
            Type::Struct {
                id: _,
                fields: _,
                w: _,
            } => panic!("Should not need to print struct types in this model."),
        }
    }
    fn forall_to_string(v: &Var, expr: String) -> String {
        let typ_str = Self::typ_to_string(&v.typ);
        format!("(forall ({}: {}) :: ({}))", &v.name[1..], typ_str, expr)
    }
    fn exists_to_string(v: &Var, expr: String) -> String {
        let typ_str = Self::typ_to_string(&v.typ);
        format!("(exists ({}: {}) :: ({}))", &v.name[1..], typ_str, expr)
    }
    fn deref_app_to_string(bytes: u64, ptr: String, old: bool) -> String {
        format!(
            "deref_{}({}(mem), {})",
            bytes,
            if old { "old" } else { "" },
            ptr
        )
    }
    fn comp_app_to_string(compop: &CompOp, e1: Option<String>, e2: Option<String>) -> String {
        match compop {
            CompOp::Equality => format!("({} == {})", e1.unwrap(), e2.unwrap()),
            CompOp::Inequality => format!("({} != {})", e1.unwrap(), e2.unwrap()),
            CompOp::Lt => format!("({} < {})", e1.unwrap(), e2.unwrap()),
            CompOp::Le => format!("({} <= {})", e1.unwrap(), e2.unwrap()),
            CompOp::Gt => format!("({} > {})", e1.unwrap(), e2.unwrap()),
            CompOp::Ge => format!("({} >= {})", e1.unwrap(), e2.unwrap()),
            CompOp::Ltu => format!("({} <_u {})", e1.unwrap(), e2.unwrap()),
            CompOp::Leu => format!("({} <=_u {})", e1.unwrap(), e2.unwrap()),
            CompOp::Gtu => format!("({} >_u {})", e1.unwrap(), e2.unwrap()),
            CompOp::Geu => format!("({} >=_u {})", e1.unwrap(), e2.unwrap()),
        }
    }
    fn bv_app_to_string(bvop: &BVOp, e1: Option<String>, e2: Option<String>) -> String {
        match bvop {
            BVOp::Add => format!("({} + {})", e1.unwrap(), e2.unwrap()),
            BVOp::Sub => format!("({} - {})", e1.unwrap(), e2.unwrap()),
            BVOp::Mul => format!("({} * {})", e1.unwrap(), e2.unwrap()),
            BVOp::And => format!("({} & {})", e1.unwrap(), e2.unwrap()),
            BVOp::Or => format!("({} | {})", e1.unwrap(), e2.unwrap()),
            BVOp::Xor => format!("({} ^ {})", e1.unwrap(), e2.unwrap()),
            BVOp::Not => format!("~{}", e1.unwrap()),
            BVOp::UnaryMinus => format!("-{}", e1.unwrap()),
            BVOp::SignExt => match e2.unwrap().split("bv").next().unwrap() {
                width if width != "0" => format!("bv_sign_extend({}, {})", width, e1.unwrap()),
                _ => format!("{}", e1.unwrap()),
            },
            BVOp::ZeroExt => match e2.unwrap().split("bv").next().unwrap() {
                width if width != "0" => format!("bv_zero_extend({}, {})", width, e1.unwrap()),
                _ => format!("{}", e1.unwrap()),
            },
            BVOp::LeftShift => format!("bv_left_shift({}, {})", e2.unwrap(), e1.unwrap()),
            BVOp::RightShift => format!("bv_l_right_shift({}, {})", e2.unwrap(), e1.unwrap()),
            BVOp::Concat => format!("({} ++ {})", e1.unwrap(), e2.unwrap()),
            BVOp::Slice { l, r } => format!("{}[{}:{}]", e1.unwrap(), l, r),
            _ => panic!("[bvop_to_string] Unimplemented."),
        }
    }
    fn bool_app_to_string(bop: &BoolOp, e1: Option<String>, e2: Option<String>) -> String {
        match bop {
            BoolOp::Conj => format!("({} && {})", e1.unwrap(), e2.unwrap()),
            BoolOp::Disj => format!("({} || {})", e1.unwrap(), e2.unwrap()),
            BoolOp::Iff => format!("({} <==> {})", e1.unwrap(), e2.unwrap()),
            BoolOp::Impl => format!("({} ==> {})", e1.unwrap(), e2.unwrap()),
            BoolOp::Neg => format!("!{}", e1.unwrap()),
        }
    }
    fn fapp_to_string(fapp: &FuncApp) -> String {
        format!(
            "{}({})",
            fapp.func_name,
            fapp.operands
                .iter()
                .map(|x| { Self::expr_to_string(&*x) })
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
    fn array_index_to_string(e1: String, e2: String) -> String {
        format!("{}[{}]", e1, e2)
    }
    fn get_field_to_string(e1: String, field: String) -> String {
        format!("{}.{}", e1, field)
    }

    /// Statements to string
    fn stmt_to_string(stmt: &Stmt) -> String {
        match stmt {
            Stmt::Skip => Self::skip_to_string(),
            Stmt::Assert(expr) => Self::assert_to_string(&expr),
            Stmt::Assume(expr) => Self::assume_to_string(&expr),
            Stmt::Havoc(var) => Self::havoc_to_string(var),
            Stmt::FuncCall(fc) => Self::func_call_to_string(&fc),
            Stmt::Assign(assign) => Self::assign_to_string(&assign),
            Stmt::IfThenElse(ite) => Self::ite_to_string(&ite),
            Stmt::Block(stmt_vec) => Self::block_to_string(&stmt_vec),
        }
    }
    fn skip_to_string() -> String {
        format!("")
    }
    fn assert_to_string(expr: &Expr) -> String {
        format!("assert ({});", Self::expr_to_string(expr))
    }
    fn assume_to_string(expr: &Expr) -> String {
        format!("assume ({});", Self::expr_to_string(expr))
    }
    fn havoc_to_string(var: &Rc<Var>) -> String {
        format!("havoc {};", Self::var_to_string(&*var))
    }
    fn func_call_to_string(func_call: &FuncCall) -> String {
        let lhs = func_call
            .lhs
            .iter()
            .map(|rc_expr| Self::expr_to_string(&*rc_expr))
            .collect::<Vec<_>>()
            .join(", ");
        let args = func_call
            .operands
            .iter()
            .map(|rc_expr| {
                let expr_str = Self::expr_to_string(&*rc_expr);
                if expr_str == "zero" {
                    format!("to_xlen_t(0bv64)")
                } else {
                    expr_str
                }
            })
            .collect::<Vec<_>>()
            .join(", ");
        format!(
            "call ({}) = {}({});",
            lhs,
            func_call.func_name.replace(".", "_"),
            args
        )
    }
    fn assign_to_string(assign: &Assign) -> String {
        let lhs = assign
            .lhs
            .iter()
            .map(|rc_expr| Self::expr_to_string(&*rc_expr))
            .collect::<Vec<_>>()
            .join(", ");
        let rhs = assign
            .rhs
            .iter()
            .map(|rc_expr| Self::expr_to_string(&*rc_expr))
            .collect::<Vec<_>>()
            .join(", ");
        format!("{} = {};", lhs, rhs)
    }
    fn ite_to_string(ite: &IfThenElse) -> String {
        let cond = Self::expr_to_string(&ite.cond);
        let thn = utils::indent_text(Self::stmt_to_string(&*ite.then_stmt), 4);
        let els = if let Some(else_stmt) = &ite.else_stmt {
            format!(
                "else {{\n{}\n}}",
                utils::indent_text(Self::stmt_to_string(&*else_stmt), 4)
            )
        } else {
            String::from("")
        };
        format!("if ({}) {{\n{}\n}}{}", cond, thn, els)
    }
    fn block_to_string(blk: &Vec<Box<Stmt>>) -> String {
        let inner = blk
            .iter()
            .map(|rc_stmt| Self::stmt_to_string(rc_stmt))
            .collect::<Vec<_>>()
            .join("\n");
        let inner = utils::indent_text(inner, 4);
        format!("{{\n{}\n}}", inner)
    }
    fn func_model_to_string(fm: &FuncModel, dwarf_ctx: &DwarfCtx) -> String {
        let args = fm
            .sig
            .arg_decls
            .iter()
            .map(|var| Self::var_decl(&var.get_expect_var()))
            .collect::<Vec<_>>()
            .join(", ");
        let ret = if let Some(rd) = &fm.sig.ret_decl {
            format!("returns ({})", Self::var_decl(rd.get_expect_var()))
        } else {
            format!("")
        };
        let requires = fm
            .sig
            .requires
            .iter()
            .map(|spec| {
                format!(
                    "\n    requires ({});",
                    Self::spec_expr_to_string(
                        &fm.sig.name[..],
                        spec.expr(),
                        dwarf_ctx,
                        spec.expr().contains_old()
                    )
                )
            })
            .collect::<Vec<_>>()
            .join("");
        let ensures = fm
            .sig
            .ensures
            .iter()
            .map(|spec| {
                format!(
                    "\n    ensures ({});",
                    Self::spec_expr_to_string(
                        &fm.sig.name[..],
                        spec.expr(),
                        dwarf_ctx,
                        spec.expr().contains_old()
                    )
                )
            })
            .collect::<Vec<_>>()
            .join("");
        let modifies = if fm.sig.mod_set.len() > 0 {
            format!(
                "\n    modifies {};",
                fm.sig
                    .mod_set
                    .iter()
                    .cloned()
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        } else {
            format!("")
        };
        let body = Self::block_to_string(fm.body.get_expect_block());
        let inline = if fm.inline { "[inline] " } else { "" };
        format!(
            "procedure {}{}({}){}{}{}{}\n{}",
            inline, fm.sig.name, args, ret, modifies, requires, ensures, body
        )
    }

    // Generate function model
    // NOTE: Replace string with write to file
    fn model_to_string(
        xlen: &u64,
        model: &Model,
        dwarf_ctx: &DwarfCtx,
        ignored_funcs: &HashSet<&str>,
    ) -> String {
        let xlen_defn = utils::indent_text(
            format!(
                "type xlen_t = bv{};\ndefine to_xlen_t(x: bv64): xlen_t = x[{}:0];",
                xlen,
                xlen - 1
            ),
            4,
        );
        // prelude
        let prelude = Self::prelude();
        // variables
        let var_defns = utils::indent_text(Self::gen_var_defns(model), 4);
        // definitions
        let array_defns = Self::gen_array_defns(&dwarf_ctx); // Define macros that index for arrays (by muiltiplication)
        let struct_defns = Self::gen_struct_defns(&dwarf_ctx); // Define macros for getting struct field values
        let global_var_defns = Self::gen_global_defns(&dwarf_ctx); // Define macros for global variable pointers
        let global_func_defns = Self::gen_global_func_defns(&model); // Define macros for function addresses                                              // procedures
        let procs = Self::gen_procs(model, &dwarf_ctx);
        // control block
        let ctrl_blk = Self::control_blk(model, &dwarf_ctx, ignored_funcs);
        format!(
            "module {} {{\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n{}\n\n{}\n}}",
            model.name,
            xlen_defn,
            prelude,
            var_defns,
            array_defns,
            struct_defns,
            global_var_defns,
            global_func_defns,
            procs,
            ctrl_blk
        )
    }

    /// Specification langauge translation functions
    fn spec_fapp_to_string(name: &str, fapp: &FuncApp, dwarf_ctx: &DwarfCtx) -> String {
        format!(
            "{}({})",
            fapp.func_name,
            fapp.operands
                .iter()
                .map(|x| Self::spec_expr_to_string(name, &*x, dwarf_ctx, false))
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
    fn spec_opapp_to_string(
        func_name: &str,
        opapp: &OpApp,
        dwarf_ctx: &DwarfCtx,
        old: bool,
    ) -> String {
        let e1_str = opapp.operands.get(0).map_or(None, |e| {
            Some(Self::spec_expr_to_string(func_name, e, dwarf_ctx, old))
        });
        let e2_str = opapp.operands.get(1).map_or(None, |e| {
            Some(Self::spec_expr_to_string(func_name, e, dwarf_ctx, old))
        });
        match &opapp.op {
            Op::Forall(v) => Self::forall_to_string(v, e1_str.unwrap()),
            Op::Exists(v) => Self::exists_to_string(v, e1_str.unwrap()),
            Op::Deref(width) => {
                Self::deref_app_to_string(width / utils::BYTE_SIZE, e1_str.unwrap(), old)
            }
            Op::Old => Self::spec_expr_to_string(
                func_name,
                opapp
                    .operands
                    .get(0)
                    .expect("Old operator is missing an expression."),
                dwarf_ctx,
                true,
            ),
            Op::Comp(cop) => Self::comp_app_to_string(cop, e1_str, e2_str),
            Op::Bv(bvop) => Self::bv_app_to_string(bvop, e1_str, e2_str),
            Op::Bool(bop) => Self::bool_app_to_string(bop, e1_str, e2_str),
            Op::ArrayIndex => {
                // Memory index is just the address itself
                if opapp.operands[0].get_expect_var().name == system_model::MEM_VAR {
                    return Self::spec_expr_to_string(
                        func_name,
                        &opapp.operands[1],
                        dwarf_ctx,
                        old,
                    );
                }
                // Get expression expression type
                let array = e1_str.unwrap();
                let index = e2_str.unwrap();
                let index_var = opapp.operands[1].typ();
                let index_var_width = index_var.get_expect_bv_width();
                let out_typ = opapp.operands[0].typ().get_array_out_type();
                let out_typ_width = out_typ.get_expect_bv_width();
                let in_typ = &opapp.operands[0].typ().get_array_in_type()[0];
                let in_typ_width = in_typ.get_expect_bv_width();
                format!(
                    "{}({}, {})",
                    Self::array_index_macro_name(&(out_typ_width / utils::BYTE_SIZE)),
                    array,
                    Self::extend_to_match_width(
                        &index,
                        index_var_width, // from
                        in_typ_width,    // to
                    )
                )
            }
            Op::GetField(field) => {
                let typ = opapp.operands[0].typ();
                let struct_id = typ.get_struct_id();
                format!(
                    "{}({})",
                    Self::get_field_macro_name(&struct_id, field),
                    e1_str.unwrap()
                )
            }
        }
    }

    /// Specification variable to Uclid5 variable
    /// Globals are shadowed by function variables
    fn spec_var_to_string(_func_name: &str, v: &Var, dwarf_ctx: &DwarfCtx, old: bool) -> String {
        if v.name.chars().next().unwrap() == '$' {
            let name = &v.name[1..];
            if name == "ret" {
                format!("{}(a0)", if old { "old" } else { "" },)
            } else {
                format!("{}({})", if old { "old" } else { "" }, name)
            }
        } else if dwarf_ctx
            .func_sigs()
            .iter()
            .find(|(_, fs)| fs.args.iter().find(|arg| arg.name == v.name).is_some())
            .is_some()
            || system_model::SYSTEM_VARS.contains(&&v.name[..])
        {
            format!("{}({})", if old { "old" } else { "" }, v.name.clone())
        } else if dwarf_ctx
            .global_vars()
            .iter()
            .find(|x| x.name == v.name)
            .is_some()
        {
            format!("{}()", utils::global_var_ptr_name(&v.name[..]))
        } else {
            panic!("Unable to find variable {:?}", v);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type U5I = Uclid5Interface<CDwarfInterface>;

    #[test]
    fn test_lit_to_string() {
        let bv_lit = Literal::Bv { val: 0, width: 1 };
        assert_eq!(U5I::lit_to_string(&bv_lit), "0bv1");
    }

    #[test]
    fn test_assign_to_string() {
        let bv64_type = Type::Bv { w: 64 };
        let var_x = Expr::Var(Var {
            name: "x".to_string(),
            typ: bv64_type,
        });
        let bv_lit = Expr::Literal(Literal::Bv { val: 0, width: 64 });
        let assign = Assign {
            lhs: vec![var_x],
            rhs: vec![bv_lit],
        };
        assert_eq!(U5I::assign_to_string(&assign), "x = 0bv64;");
    }
}
