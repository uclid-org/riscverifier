use std::rc::Rc;
use std::collections::HashSet;
use std::fmt;

use crate::ast;
use crate::readers::dwarfreader::DwarfCtx;

// =====================================================================================================
/// IR Interface
/// 
/// This intermediate representation (IR) interface
/// contains the function declarations to define for a
/// verification engine

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
        let e1_str = opapp
            .operands
            .get(0)
            .map_or(None, |e| Some(Self::expr_to_string(e, xlen)));
        let e2_str = opapp
            .operands
            .get(1)
            .map_or(None, |e| Some(Self::expr_to_string(e, xlen)));
        match &opapp.op {
            ast::Op::Forall(v) => Self::forall_to_string(v, e1_str.unwrap()),
            ast::Op::Exists(v) => Self::exists_to_string(v, e1_str.unwrap()),
            ast::Op::Deref(_) => panic!("Deref is only supported in the specification."),
            ast::Op::Old => panic!("Old operator is only supported in the specification."),
            ast::Op::Comp(cop) => Self::comp_app_to_string(cop, e1_str, e2_str),
            ast::Op::Bv(bvop) => Self::bv_app_to_string(bvop, e1_str, e2_str),
            ast::Op::Bool(bop) => Self::bool_app_to_string(bop, e1_str, e2_str),
            ast::Op::ArrayIndex => Self::array_index_to_string(e1_str.unwrap(), e2_str.unwrap()),
            ast::Op::GetField(field) => Self::get_field_to_string(e1_str.unwrap(), field.clone()),
        }
    }
    fn fapp_to_string(fapp: &ast::FuncApp, xlen: &u64) -> String;
    fn var_to_string(v: &ast::Var) -> String {
        format!("{}", v.name)
    }
    fn lit_to_string(lit: &ast::Literal) -> String;
    fn typ_to_string(typ: &ast::Type) -> String;
    fn forall_to_string(v: &ast::Var, expr: String) -> String;
    fn exists_to_string(v: &ast::Var, expr: String) -> String;
    fn deref_app_to_string(bytes: u64, e1: String, old: bool) -> String;
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