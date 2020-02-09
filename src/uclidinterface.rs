use std::fmt;
use std::rc::Rc;

use crate::ir::*;
use crate::translator::*;
use crate::utils::*;

#[derive(Debug)]
pub struct Uclid5Interface;

impl Uclid5Interface {
    pub fn new() -> Self {
        Uclid5Interface {}
    }
    fn gen_var_defns(model: &Model) -> String {
        let mut defn_string = String::from("");
        let mut sorted = model.vars.iter().collect::<Vec<_>>();
        sorted.sort();
        for v in sorted.iter() {
            let var_defn = Self::var_decl(&v);
            defn_string = format!("{}\n{}", defn_string, var_defn);
        }
        defn_string
    }
    fn gen_array_defns(model: &Model) -> String {
        format!("")
    }
    fn gen_struct_defns(model: &Model) -> String {
        format!("")
    }
    fn gen_global_defns(model: &Model) -> String {
        format!("")
    }
    fn gen_procs(model: &Model) -> String {
        let procs_string = model
            .func_models
            .iter()
            .map(|fm| Self::func_model_to_string(fm))
            .collect::<Vec<_>>()
            .join("\n\n");
        indent_text(procs_string, 4)
    }
    fn control_blk(model: &Model) -> String {
        let verif_fns_string = model
            .func_models
            .iter()
            .map(|fm| {
                format!(
                    "// f{} = verify({});",
                    fm.sig.name.clone(),
                    fm.sig.name.clone()
                )
            })
            .collect::<Vec<_>>()
            .join("\n");
        let verif_fns_string = indent_text(verif_fns_string, 4);
        let control_string = format!("control {{\n{}\n}}", verif_fns_string);
        indent_text(control_string, 4)
    }
    /// Helper functions
    fn var_decl(var: &Var) -> String {
        format!(
            "var {}: {};",
            Self::var_to_string(var),
            Self::typ_to_string(&*var.typ)
        )
    }
}

impl IRInterface for Uclid5Interface {
    fn lit_to_string(lit: &Literal) -> String {
        match lit {
            Literal::Bv { val, width } => format!("{}bv{}", val, width),
            Literal::Bool { val } => format!("{}", val),
        }
    }
    fn typ_to_string(typ: &Type) -> String {
        match typ {
            Type::Bool => format!("bool"),
            Type::Bv { w } => format!("bv{}", w),
            Type::Array { in_typs, out_typ } => format!(
                "[{}]{}",
                in_typs
                    .iter()
                    .map(|typ| Self::typ_to_string(typ))
                    .collect::<Vec<_>>()
                    .join(", "),
                Self::typ_to_string(out_typ)
            ), // FIXME
        }
    }
    fn comp_app_to_string(compop: &CompOp, e1: Option<String>, e2: Option<String>) -> String {
        match compop {
            CompOp::Equality => format!("{} == {}", e1.unwrap(), e2.unwrap()),
            CompOp::Inequality => format!("{} != {}", e1.unwrap(), e2.unwrap()),
        }
    }
    fn bv_app_to_string(bvop: &BVOp, e1: Option<String>, e2: Option<String>) -> String {
        match bvop {
            BVOp::Lt => format!("{} < {}", e1.unwrap(), e2.unwrap()),
            BVOp::Le => format!("{} <= {}", e1.unwrap(), e2.unwrap()),
            BVOp::Gt => format!("{} > {}", e1.unwrap(), e2.unwrap()),
            BVOp::Ge => format!("{} >= {}", e1.unwrap(), e2.unwrap()),
            BVOp::Ltu => format!("{} <_u {}", e1.unwrap(), e2.unwrap()),
            BVOp::Leu => format!("{} <=_u {}", e1.unwrap(), e2.unwrap()),
            BVOp::Gtu => format!("{} >_u {}", e1.unwrap(), e2.unwrap()),
            BVOp::Geu => format!("{} >=_u {}", e1.unwrap(), e2.unwrap()),
            BVOp::Add => format!("{} + {}", e1.unwrap(), e2.unwrap()),
            BVOp::Sub => format!("{} - {}", e1.unwrap(), e2.unwrap()),
            BVOp::Mul => format!("{} * {}", e1.unwrap(), e2.unwrap()),
            BVOp::And => format!("{} & {}", e1.unwrap(), e2.unwrap()),
            BVOp::Or => format!("{} | {}", e1.unwrap(), e2.unwrap()),
            BVOp::Xor => format!("{} ^ {}", e1.unwrap(), e2.unwrap()),
            BVOp::Not => format!("~{}", e1.unwrap()),
            BVOp::UnaryMinus => format!("-{}", e1.unwrap()),
            BVOp::SignExt => format!("bv_sign_ext({}, {})", e2.unwrap(), e1.unwrap()),
            BVOp::ZeroExt => format!("bv_zero_ext({}, {})", e2.unwrap(), e1.unwrap()),
            BVOp::LeftShift => format!("bv_l_shift()"),
            _ => panic!("[bvop_to_string] Unimplemented."),
        }
    }
    fn bool_app_to_string(bop: &BoolOp, e1: Option<String>, e2: Option<String>) -> String {
        match bop {
            BoolOp::Conj => format!("{} && {}", e1.unwrap(), e2.unwrap()),
            BoolOp::Disj => format!("{} || {}", e1.unwrap(), e2.unwrap()),
            BoolOp::Iff => format!("{} <==> {}", e1.unwrap(), e2.unwrap()),
            BoolOp::Impl => format!("{} ==> {}", e1.unwrap(), e2.unwrap()),
            BoolOp::Neg => format!("!{}", e1.unwrap()),
        }
    }
    fn fapp_to_string(fapp: &FuncApp) -> String {
        format!(
            "{}({})",
            fapp.func_name,
            fapp.operands
                .iter()
                .map(|x| Self::expr_to_string(&*x))
                .collect::<Vec<String>>()
                .join(", ")
        )
    }
    fn array_index_to_string(e1: String, e2: String) -> String {
        format!("{}[{}]", e1, e2)
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
            .map(|rc_expr| Self::expr_to_string(&*rc_expr))
            .collect::<Vec<_>>()
            .join(", ");
        format!("call ({}) = {}({});", lhs, func_call.func_name, args)
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
        let thn = indent_text(Self::stmt_to_string(&*ite.then_stmt), 4);
        let els = if let Some(else_stmt) = &ite.else_stmt {
            format!(
                "else {{\n{}\n}}",
                indent_text(Self::stmt_to_string(&*else_stmt), 4)
            )
        } else {
            String::from("")
        };
        format!("if ({}) {{\n{}\n}}{}", cond, thn, els)
    }
    fn block_to_string(blk: &Vec<Rc<Stmt>>) -> String {
        let inner = blk
            .iter()
            .map(|rc_stmt| Self::stmt_to_string(rc_stmt))
            .collect::<Vec<_>>()
            .join("\n");
        let inner = indent_text(inner, 4);
        format!("{{\n{}\n}}", inner)
    }
    fn func_model_to_string(fm: &FuncModel) -> String {
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
            .map(|e| format!("\nrequires ({});", Self::expr_to_string(e)))
            .collect::<Vec<_>>()
            .join("");
        let ensures = fm
            .sig
            .ensures
            .iter()
            .map(|e| format!("\nensures ({});", Self::expr_to_string(e)))
            .collect::<Vec<_>>()
            .join("");
        let modifies = if fm.sig.mod_set.len() > 0 {
            format!(
                "\nmodifies {};",
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
    fn ir_model_to_string(model: &Model) -> String {
        // prelude
        // variables
        let var_defns = indent_text(Self::gen_var_defns(model), 4);
        // definitions
        let array_defns = Self::gen_array_defns(model);
        let struct_defns = Self::gen_struct_defns(model);
        let global_defns = Self::gen_global_defns(model);
        // procedures
        let procs = Self::gen_procs(model);
        // control block
        let ctrl_blk = Self::control_blk(model);
        format!(
            "module main {{\n{}\n{}\n{}\n{}\n{}\n\n{}\n}}",
            var_defns, array_defns, struct_defns, global_defns, procs, ctrl_blk
        )
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    type U5I = Uclid5Interface;

    #[test]
    fn test_lit_to_string() {
        let bv_lit = Literal::Bv { val: 0, width: 1 };
        assert_eq!(U5I::lit_to_string(&bv_lit), "0bv1");
    }

    #[test]
    fn test_assign_to_string() {
        let bv64_type = Rc::new(Type::Bv { w: 64 });
        let var_x = Rc::new(Expr::Var(Var {
            name: "x",
            typ: bv64_type,
        }));
        let bv_lit = Rc::new(Expr::Literal(Literal::Bv { val: 0, width: 64 }));
        let assign = Assign {
            lhs: vec![var_x],
            rhs: vec![bv_lit],
        };
        assert_eq!(U5I::assign_to_string(&assign), "x = 0bv64;");
    }
}
