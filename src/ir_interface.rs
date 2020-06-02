use std::rc::Rc;
use std::collections::HashSet;
use std::fmt;

use crate::readers::dwarfreader::DwarfCtx;
use crate::ast;
use crate::spec_lang::sl_ast;

// =====================================================================================================
/// IR Interface
/// Defines functions from ast (ie. ast.rs) to verification language 
pub trait IRInterface: fmt::Debug {
    /// FIXME: Rewrite all of this to translate expressions at the leaves
    ///        of the mutually recursive calls not at the root (notice
    ///        how the operands are currently translated first as 
    ///        e1_str and e2_str)

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
        let e1_str = opapp
            .operands
            .get(0)
            .map_or(None, |e| Some(Self::expr_to_string(e, xlen)));
        let e2_str = opapp
            .operands
            .get(1)
            .map_or(None, |e| Some(Self::expr_to_string(e, xlen)));
        match &opapp.op {
            ast::Op::Comp(cop) => Self::comp_app_to_string(cop, e1_str, e2_str),
            ast::Op::Bv(bvop) => Self::bv_app_to_string(bvop, e1_str, e2_str),
            ast::Op::Bool(bop) => Self::bool_app_to_string(bop, e1_str, e2_str),
            ast::Op::ArrayIndex => Self::array_index_to_string(e1_str.unwrap(), e2_str.unwrap()),
            ast::Op::GetField(field) => Self::get_field_to_string(e1_str.unwrap(), field.clone()),
        }
    }
    fn fapp_to_string(fapp: &ast::FuncApp, xlen: &u64) -> String;
    fn var_to_string(v: &ast::Var) -> String;
    fn lit_to_string(lit: &ast::Literal) -> String;
    fn typ_to_string(typ: &ast::Type) -> String;
    fn comp_app_to_string(compop: &ast::CompOp, e1: Option<String>, e2: Option<String>) -> String;
    fn bv_app_to_string(bvop: &ast::BVOp, e1: Option<String>, e2: Option<String>) -> String;
    fn bool_app_to_string(bop: &ast::BoolOp, e1: Option<String>, e2: Option<String>) -> String;
    fn array_index_to_string(e1: String, e2: String) -> String;
    fn get_field_to_string(e1: String, field: String) -> String;
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
    // fn track_proc(fm: &FuncModel, dwarf_ctx: &DwarfCtx) -> String;
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
/// Specification language interface
/// Defines functions from spec lang ast (ie. spec_lang/sl_ast.rs) to verification langauge

pub trait SpecLangASTInterface {
    /// BExpr translation functions
    fn bexpr_to_string(expr: &sl_ast::BExpr) -> String {
        match expr {
            sl_ast::BExpr::Bool(b) => Self::bexpr_bool_to_string(b),
            sl_ast::BExpr::BOpApp(bop, exprs) => Self::bexpr_bopapp_to_string(bop, exprs),
            sl_ast::BExpr::COpApp(cop, exprs) => Self::bexpr_copapp_to_string(cop, exprs),
        }
    }
    fn bexpr_bool_to_string(b: &bool) -> String;
    fn bexpr_bopapp_to_string(bop: &sl_ast::BoolOp, exprs: &Vec<Box<sl_ast::BExpr>>) -> String;
    fn bexpr_copapp_to_string(cop: &sl_ast::CompOp, exprs: &Vec<Box<sl_ast::VExpr>>) -> String;
    fn bopp_to_string(bop: &sl_ast::BoolOp) -> String;
    fn cop_to_string(cop: &sl_ast::CompOp) -> String;
    // VExpr translation functions
    fn vexpr_to_string(expr: &sl_ast::VExpr) -> String {
        match expr {
            sl_ast::VExpr::Bv { value, width } => Self::vexpr_bv_to_string(value, width),
            sl_ast::VExpr::Int(i) => Self::vexpr_int_to_string(i),
            sl_ast::VExpr::Bool(b) => Self::vexpr_bool_to_string(b),
            sl_ast::VExpr::Var(v) => Self::vexpr_var_to_string(v),
            sl_ast::VExpr::OpApp(vop, exprs) => Self::vexpr_opapp_to_string(vop, exprs),
            sl_ast::VExpr::FuncApp(fname, args) => Self::vexpr_funcapp_to_string(fname, args),
        }
    }
    fn vexpr_bv_to_string(value: &u64, width: &u16) -> String;
    fn vexpr_int_to_string(i: &i64) -> String;
    fn vexpr_bool_to_string(b: &bool) -> String;
    fn vexpr_var_to_string(v: &String) -> String;
    fn vexpr_opapp_to_string(op: &sl_ast::ValueOp, exprs: &Vec<Box<sl_ast::VExpr>>) -> String;
    fn vexpr_funcapp_to_string(fname: &String, args: &Vec<Box<sl_ast::VExpr>>) -> String;
    fn valueop_to_string(op: &sl_ast::ValueOp) -> String;
    // Spec statement to string
    fn spec_to_string(spec: &sl_ast::Spec) -> String;
}

