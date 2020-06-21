use std::collections::HashSet;
use std::fmt;
use std::rc::Rc;

use asts::ast;
use asts::spec_lang::sl_ast;
use dwarf_ctx::dwarfreader::{DwarfCtx};

// =====================================================================================================
/// # IR Interface

/// Defines functions from ast (ie. ast.rs) to verification language
pub trait IRInterface: fmt::Debug {
    /// Expressions to string functions
    fn expr_to_string(expr: &ast::Expr, xlen: &u64) -> String {
        match expr {
            ast::Expr::Literal(l, _) => Self::lit_to_string(l),
            ast::Expr::FuncApp(fapp, _) => Self::fapp_to_string(fapp, xlen),
            ast::Expr::OpApp(opapp, _) => Self::opapp_to_string(opapp, xlen),
            ast::Expr::Var(v, _) => Self::var_to_string(v),
        }
    }
    fn opapp_to_string(opapp: &ast::OpApp, xlen: &u64) -> String {
        match &opapp.op {
            ast::Op::Comp(cop) => Self::comp_app_to_string(cop, &opapp.operands, xlen),
            ast::Op::Bv(bvop) => Self::bv_app_to_string(bvop, &opapp.operands, xlen),
            ast::Op::Bool(bop) => Self::bool_app_to_string(bop, &opapp.operands, xlen),
            ast::Op::ArrayIndex => {
                Self::array_index_to_string(&opapp.operands[0], &opapp.operands[1], xlen)
            }
            ast::Op::GetField(field) => {
                Self::get_field_to_string(&opapp.operands[0], &field.clone(), xlen)
            }
        }
    }
    fn fapp_to_string(fapp: &ast::FuncApp, xlen: &u64) -> String;
    fn var_to_string(v: &ast::Var) -> String;
    fn lit_to_string(lit: &ast::Literal) -> String;
    fn typ_to_string(typ: &ast::Type) -> String;
    fn comp_app_to_string(compop: &ast::CompOp, exprs: &Vec<ast::Expr>, xlen: &u64) -> String;
    fn bv_app_to_string(bvop: &ast::BVOp, exprs: &Vec<ast::Expr>, xlen: &u64) -> String;
    fn bool_app_to_string(bop: &ast::BoolOp, exprs: &Vec<ast::Expr>, xlen: &u64) -> String;
    fn array_index_to_string(arr: &ast::Expr, index: &ast::Expr, xlen: &u64) -> String;
    fn get_field_to_string(struct_: &ast::Expr, field: &String, xlen: &u64) -> String;
    /// Statements to string
    fn stmt_to_string(stmt: &ast::Stmt, xlen: &u64) -> String;
    fn skip_to_string() -> String;
    fn assert_to_string(expr: &ast::Expr, xlen: &u64) -> String;
    fn assume_to_string(expr: &ast::Expr, xlen: &u64) -> String;
    fn havoc_to_string(var: &Rc<ast::Var>) -> String;
    fn func_call_to_string(func_call: &ast::FuncCall, xlen: &u64) -> String;
    fn assign_to_string(assign: &ast::Assign, xlen: &u64) -> String;
    fn ite_to_string(ite: &ast::IfThenElse, xlen: &u64) -> String;
    fn block_to_string(blk: &Vec<Box<ast::Stmt>>, xlen: &u64) -> String;
    fn comment_to_string(comment: &String) -> String;
    fn func_model_to_string(fm: &ast::FuncModel, dwarf_ctx: &DwarfCtx, xlen: &u64) -> String;
    // IR to model string
    fn model_to_string(
        xlen: &u64,
        model: &ast::Model,
        dwarf_ctx: &DwarfCtx,
        ignored_funcs: &HashSet<&str>,
        verify_funcs: &Vec<&str>,
    ) -> String;
}

// =================================================================================================
/// # Specification language interface
/// Defines functions from spec lang ast (ie. spec_lang/sl_ast.rs) to verification langauge

pub trait SpecLangASTInterface: fmt::Debug {
    /// BExpr translation functions
    fn bexpr_to_string(expr: &sl_ast::BExpr) -> String {
        match expr {
            sl_ast::BExpr::Bool(b) => Self::bexpr_bool_to_string(b),
            sl_ast::BExpr::BOpApp(bop, exprs) => Self::bexpr_bopapp_to_string(bop, exprs),
            sl_ast::BExpr::COpApp(cop, exprs) => Self::bexpr_copapp_to_string(cop, exprs),
        }
    }
    fn bexpr_bool_to_string(b: &bool) -> String;
    fn bexpr_bopapp_to_string(bop: &sl_ast::BoolOp, exprs: &Vec<sl_ast::BExpr>) -> String;
    fn bexpr_copapp_to_string(cop: &sl_ast::CompOp, exprs: &Vec<sl_ast::VExpr>) -> String;
    fn bopp_to_string(bop: &sl_ast::BoolOp) -> String;
    fn cop_to_string(cop: &sl_ast::CompOp) -> String;
    // VExpr translation functions
    fn vexpr_to_string(expr: &sl_ast::VExpr) -> String {
        match expr {
            sl_ast::VExpr::Bv { value, typ } => Self::vexpr_bv_to_string(value, typ),
            sl_ast::VExpr::Int(i, _) => Self::vexpr_int_to_string(i),
            sl_ast::VExpr::Bool(b, _) => Self::vexpr_bool_to_string(b),
            sl_ast::VExpr::Ident(v, _) => Self::vexpr_ident_to_string(v),
            sl_ast::VExpr::OpApp(vop, exprs, _) => Self::vexpr_opapp_to_string(vop, exprs),
            sl_ast::VExpr::FuncApp(fname, args, _) => Self::vexpr_funcapp_to_string(fname, args),
        }
    }
    fn vexpr_bv_to_string(value: &u64, typ: &sl_ast::VType) -> String;
    fn vexpr_int_to_string(i: &i64) -> String;
    fn vexpr_bool_to_string(b: &bool) -> String;
    fn vexpr_ident_to_string(v: &String) -> String;
    fn vexpr_opapp_to_string(op: &sl_ast::ValueOp, exprs: &Vec<sl_ast::VExpr>) -> String;
    fn vexpr_funcapp_to_string(fname: &String, args: &Vec<sl_ast::VExpr>) -> String;
    fn valueop_to_string(op: &sl_ast::ValueOp) -> String;
    // Types to string
    fn vtype_to_string(typ: &sl_ast::VType) -> String;
    // Spec statement to string
    fn spec_to_string(spec: &sl_ast::Spec) -> String;
}
