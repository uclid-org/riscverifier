use std::cmp::Ordering;
use std::collections::{HashMap, HashSet};
use std::fmt;
use std::rc::Rc;

use crate::dwarfreader::{DwarfCtx, DwarfTypeDefn};
use crate::utils;

/// Types
#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Type {
    Unknown,
    Bool,
    Bv {
        w: u64,
    },
    Array {
        in_typs: Vec<Box<Type>>,
        out_typ: Box<Type>,
    },
}
impl Type {
    pub fn get_expect_bv_width(&self) -> u64 {
        match self {
            Type::Bv { w } => *w,
            _ => panic!("Not a bitvector."),
        }
    }
}

/// Expressions
#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Expr {
    Literal(Literal),
    Var(Var),
    Const(Var),
    OpApp(OpApp),
    FuncApp(FuncApp),
}
impl Expr {
    pub fn contains_old(&self) -> bool {
        match self {
            Expr::OpApp(opapp) => opapp
                .operands
                .iter()
                .fold(false, |acc, operand| acc || operand.contains_old()),
            _ => false,
        }
    }
    pub fn get_expect_var(&self) -> &Var {
        match self {
            Expr::Var(v) | Expr::Const(v) => v,
            _ => panic!("Not a variable/constant."),
        }
    }
    pub fn is_var(&self) -> bool {
        if let Expr::Var(_) = self {
            true
        } else {
            false
        }
    }
    pub fn bv_lit(val: u64, width: u64) -> Self {
        Expr::Literal(Literal::Bv { val, width })
    }
    pub fn bool_lit(val: bool) -> Self {
        Expr::Literal(Literal::Bool { val })
    }
    pub fn var(name: &str, typ: Type) -> Self {
        Expr::Var(Var {
            name: name.to_string(),
            typ,
        })
    }
    #[allow(dead_code)]
    pub fn const_var(name: &str, typ: Type) -> Self {
        Expr::Const(Var {
            name: name.to_string(),
            typ,
        })
    }
    pub fn op_app(op: Op, operands: Vec<Self>) -> Self {
        Expr::OpApp(OpApp { op, operands })
    }
    pub fn func_app(func_name: String, operands: Vec<Self>) -> Self {
        Expr::FuncApp(FuncApp {
            func_name,
            operands,
        })
    }
}
/// Literals
#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Literal {
    Bv { val: u64, width: u64 },
    Bool { val: bool },
}
#[derive(Debug, Eq, Hash, Clone)]
pub struct Var {
    pub name: String,
    pub typ: Type,
}
impl Ord for Var {
    fn cmp(&self, other: &Self) -> Ordering {
        self.name.cmp(&other.name)
    }
}
impl PartialOrd for Var {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl PartialEq for Var {
    fn eq(&self, other: &Self) -> bool {
        self.name == other.name
    }
}

// Operator application
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct OpApp {
    pub op: Op,
    pub operands: Vec<Expr>,
}
/// Operators
#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum Op {
    Deref,
    Old,
    Comp(CompOp),
    Bv(BVOp),
    Bool(BoolOp),
    ArrayIndex,
    GetField(String),
}
/// Comparison operators
#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum CompOp {
    Equality,
    Inequality,
    Lt,  // <
    Le,  // <=
    Gt,  // >
    Ge,  // >=
    Ltu, // <_u (unsigned)
    Leu, // <=_u
    Gtu, // >_u
    Geu, // >=_u
}
/// BV operators
#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum BVOp {
    Add,
    Sub,
    Mul,
    And,
    Or,
    Xor,
    Not,
    UnaryMinus,
    SignExt,
    ZeroExt,
    LeftShift,
    RightShift,
    ARightShift, // arithmetic right shift
    Slice { l: u64, r: u64 },
}
/// Boolean operators
#[allow(dead_code)]
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub enum BoolOp {
    Conj, // and: &&
    Disj, // or: ||
    Iff,  // if and only if: <==>
    Impl, // implication: ==>
    Neg,  // negation: !
}
/// Function application
#[derive(Debug, PartialEq, Eq, Hash, Clone)]
pub struct FuncApp {
    pub func_name: String,
    pub operands: Vec<Expr>,
}

/// Statements
#[allow(dead_code)]
#[derive(Debug, Clone)]
pub enum Stmt {
    Skip,
    Assert(Expr),
    Assume(Expr),
    Havoc(Rc<Var>),
    FuncCall(FuncCall),
    Assign(Assign),
    IfThenElse(IfThenElse),
    Block(Vec<Box<Stmt>>),
}
impl Stmt {
    pub fn get_expect_block(&self) -> &Vec<Box<Stmt>> {
        match self {
            Stmt::Block(b) => b,
            _ => panic!("Not a block."),
        }
    }
    pub fn is_blk(&self) -> bool {
        if let Stmt::Block(_) = self {
            true
        } else {
            false
        }
    }
    pub fn func_call(func_name: String, lhs: Vec<Expr>, operands: Vec<Expr>) -> Self {
        Stmt::FuncCall(FuncCall {
            func_name,
            lhs,
            operands,
        })
    }
    pub fn if_then_else(cond: Expr, then_stmt: Box<Stmt>, else_stmt: Option<Box<Stmt>>) -> Self {
        Stmt::IfThenElse(IfThenElse {
            cond,
            then_stmt,
            else_stmt,
        })
    }
}

/// Function call statement
#[derive(Debug, Clone)]
pub struct FuncCall {
    pub func_name: String,
    pub lhs: Vec<Expr>,
    pub operands: Vec<Expr>,
}
/// Assign statement
#[derive(Debug, Clone)]
pub struct Assign {
    pub lhs: Vec<Expr>,
    pub rhs: Vec<Expr>,
}
/// If then else statement
#[derive(Debug, Clone)]
pub struct IfThenElse {
    pub cond: Expr,
    pub then_stmt: Box<Stmt>,
    pub else_stmt: Option<Box<Stmt>>,
}
/// Verification model datatypes
#[derive(Debug, Clone)]
pub struct FuncModel {
    pub sig: FuncSig,
    pub body: Stmt,
    pub inline: bool,
}
/// Function Model for pre/post verification
impl FuncModel {
    pub fn new(
        name: &str,
        entry_addr: u64,
        arg_decls: Vec<Expr>,
        ret_decl: Option<Expr>,
        requires: Option<Vec<Spec>>,
        ensures: Option<Vec<Spec>>,
        mod_set: Option<HashSet<String>>,
        body: Stmt,
        inline: bool,
    ) -> Self {
        assert!(
            &body.is_blk(),
            format!("Body of {} should be a block.", name)
        );
        let mod_set = mod_set.unwrap_or(HashSet::new());
        let requires = requires.unwrap_or(vec![]);
        let ensures = ensures.unwrap_or(vec![]);
        FuncModel {
            sig: FuncSig::new(name, entry_addr, arg_decls, ret_decl, requires, ensures, mod_set),
            body: body,
            inline: inline,
        }
    }
}
/// Function signature
#[derive(Debug, Clone)]
pub struct FuncSig {
    pub name: String,
    pub entry_addr: u64,
    pub arg_decls: Vec<Expr>,
    pub ret_decl: Option<Expr>,
    pub requires: Vec<Spec>,
    pub ensures: Vec<Spec>,
    pub mod_set: HashSet<String>,
}
impl FuncSig {
    pub fn new(
        name: &str,
        entry_addr: u64,
        arg_decls: Vec<Expr>,
        ret_decl: Option<Expr>,
        requires: Vec<Spec>,
        ensures: Vec<Spec>,
        mod_set: HashSet<String>,
    ) -> Self {
        assert!(
            arg_decls.iter().all(|v| v.is_var()),
            format!("An argument of {} is not a variable.", name)
        );
        if let Some(rd) = &ret_decl {
            assert!(
                rd.is_var(),
                format!("The return value of {} is {:?}; not a variable.", name, rd)
            );
        }
        FuncSig {
            name: String::from(name),
            entry_addr,
            arg_decls,
            ret_decl,
            requires,
            ensures,
            mod_set,
        }
    }
}
#[derive(Debug, Clone)]
pub enum Spec {
    Requires(Expr),
    Ensures(Expr),
    Modifies(HashSet<Var>),
}
impl Spec {
    pub fn expr(&self) -> &Expr {
        match &self {
            Spec::Requires(e) | Spec::Ensures(e) => e,
            _ => panic!("Spec does not contain an expression."),
        }
    }
    pub fn mod_set(&self) -> &HashSet<Var> {
        match &self {
            Spec::Modifies(hs) => hs,
            _ => panic!("Spec is not a modifies statement."),
        }
    }
    pub fn is_requires(&self) -> bool {
        if let Spec::Requires(_) = self {
            true
        } else {
            false
        }
    }
    pub fn is_ensures(&self) -> bool {
        if let Spec::Ensures(_) = self {
            true
        } else {
            false
        }
    }
    pub fn is_modifies(&self) -> bool {
        if let Spec::Modifies(_) = self {
            true
        } else {
            false
        }
    }
}
/// Verification Model
#[derive(Debug)]
pub struct Model {
    pub vars: HashSet<Var>,
    pub func_models: Vec<FuncModel>,
}
impl Model {
    pub fn new() -> Self {
        Model {
            vars: HashSet::new(),
            func_models: vec![],
        }
    }
    pub fn add_func_model(&mut self, fm: FuncModel) {
        self.func_models.push(fm);
    }
    pub fn add_func_models(&mut self, fms: Vec<FuncModel>) {
        for fm in fms {
            self.add_func_model(fm);
        }
    }
    pub fn add_var(&mut self, var: Var) {
        self.vars.insert(var);
    }
    pub fn add_vars(&mut self, vars: &Vec<Var>) {
        for v in vars.iter() {
            self.add_var(v.clone());
        }
    }
}

/// This intermediate representation (IR) interface
/// contains the function declarations to define for a
/// verification engine
pub trait IRInterface: fmt::Debug {
    /// Expressions to string functions
    fn expr_to_string(expr: &Expr) -> String {
        match expr {
            Expr::Literal(l) => Self::lit_to_string(l),
            Expr::FuncApp(fapp) => Self::fapp_to_string(fapp),
            Expr::OpApp(opapp) => Self::opapp_to_string(opapp),
            Expr::Var(v) | Expr::Const(v) => Self::var_to_string(v),
        }
    }
    fn opapp_to_string(opapp: &OpApp) -> String {
        let e1_str = opapp
            .operands
            .get(0)
            .map_or(None, |e| Some(Self::expr_to_string(e)));
        let e2_str = opapp
            .operands
            .get(1)
            .map_or(None, |e| Some(Self::expr_to_string(e)));
        match &opapp.op {
            Op::Deref => panic!("Deref is only supported in the specification."),
            Op::Old => panic!("Old operator is only supported in the specification."),
            Op::Comp(cop) => Self::comp_app_to_string(cop, e1_str, e2_str),
            Op::Bv(bvop) => Self::bv_app_to_string(bvop, e1_str, e2_str),
            Op::Bool(bop) => Self::bool_app_to_string(bop, e1_str, e2_str),
            Op::ArrayIndex => Self::array_index_to_string(e1_str.unwrap(), e2_str.unwrap()),
            Op::GetField(field) => Self::get_field_to_string(e1_str.unwrap(), field.clone()),
        }
    }
    fn fapp_to_string(fapp: &FuncApp) -> String;
    fn var_to_string(v: &Var) -> String {
        format!("{}", v.name)
    }
    fn lit_to_string(lit: &Literal) -> String;
    fn typ_to_string(typ: &Type) -> String;
    fn deref_app_to_string(bytes: u64, e1: String, old: bool) -> String;
    fn comp_app_to_string(compop: &CompOp, e1: Option<String>, e2: Option<String>) -> String;
    fn bv_app_to_string(bvop: &BVOp, e1: Option<String>, e2: Option<String>) -> String;
    fn bool_app_to_string(bop: &BoolOp, e1: Option<String>, e2: Option<String>) -> String;
    fn array_index_to_string(e1: String, e2: String) -> String;
    fn get_field_to_string(e1: String, field: String) -> String;
    /// Statements to string
    fn stmt_to_string(stmt: &Stmt) -> String;
    fn skip_to_string() -> String;
    fn assert_to_string(expr: &Expr) -> String;
    fn assume_to_string(expr: &Expr) -> String;
    fn havoc_to_string(var: &Rc<Var>) -> String;
    fn func_call_to_string(func_call: &FuncCall) -> String;
    fn assign_to_string(assign: &Assign) -> String;
    fn ite_to_string(ite: &IfThenElse) -> String;
    fn block_to_string(blk: &Vec<Box<Stmt>>) -> String;
    fn func_model_to_string(fm: &FuncModel, dwarf_ctx: &DwarfCtx) -> String;
    // IR to model string
    fn model_to_string(xlen: &u64, model: &Model, dwarf_ctx: &DwarfCtx) -> String;
    // Specification langauge
    fn spec_expr_to_string(
        func_name: &str,
        expr: &Expr,
        dwarf_ctx: &DwarfCtx,
        old: bool,
    ) -> String {
        match expr {
            Expr::Literal(l) => Self::lit_to_string(l),
            Expr::FuncApp(fapp) => Self::spec_fapp_to_string(func_name, fapp, dwarf_ctx),
            Expr::OpApp(opapp) => Self::spec_opapp_to_string(func_name, opapp, dwarf_ctx, old),
            Expr::Var(v) | Expr::Const(v) => Self::spec_var_to_string(func_name, v, dwarf_ctx, old),
        }
    }
    fn spec_fapp_to_string(func_name: &str, fapp: &FuncApp, dwarf_ctx: &DwarfCtx) -> String;
    fn spec_opapp_to_string(
        func_name: &str,
        opapp: &OpApp,
        dwarf_ctx: &DwarfCtx,
        old: bool,
    ) -> String;
    fn spec_var_to_string(func_name: &str, v: &Var, dwarf_ctx: &DwarfCtx, old: bool) -> String;
    fn get_expr_type(
        func_name: &str,
        expr: &Expr,
        typ_map: &HashMap<String, Rc<DwarfTypeDefn>>,
    ) -> Rc<DwarfTypeDefn> {
        match expr {
            Expr::Literal(l) => match l {
                Literal::Bv { val: _, width } => Rc::new(DwarfTypeDefn::Primitive {
                    bytes: width / utils::BYTE_SIZE,
                }),
                Literal::Bool { val: _ } => Rc::new(DwarfTypeDefn::Primitive { bytes: 1 }),
            },
            Expr::Var(v) | Expr::Const(v) => {
                // Try finding variable type as a global
                if let Some(typ) = typ_map.get(&v.name) {
                    Rc::clone(typ)
                } else {
                    // Try finding variable type as function argument
                    Rc::clone(typ_map.get(&format!("{}${}", func_name, v.name)).expect(
                        &format!(
                            "Could not find type for {} in function {}.",
                            v.name, func_name
                        )[..],
                    ))
                }
            }
            Expr::OpApp(opapp) => match &opapp.op {
                Op::Comp(_) | Op::Bool(_) => Rc::new(DwarfTypeDefn::Primitive { bytes: 1 }),
                Op::Bv(_) | Op::Old | Op::Deref => {
                    Self::get_expr_type(func_name, &opapp.operands[0], typ_map)
                }
                Op::ArrayIndex => {
                    let pred_typ = Self::get_expr_type(func_name, &opapp.operands[0], typ_map);
                    match &*pred_typ {
                        DwarfTypeDefn::Array {
                            in_typ: _,
                            out_typ,
                            bytes: _,
                        } => Rc::clone(&out_typ),
                        DwarfTypeDefn::Pointer {
                            value_typ,
                            bytes: _,
                        } => Rc::clone(&value_typ),
                        _ => panic!("Should be an array type!"),
                    }
                }
                Op::GetField(s) => {
                    let pred_typ = Self::get_expr_type(func_name, &opapp.operands[0], typ_map);
                    match &*pred_typ {
                        DwarfTypeDefn::Struct {
                            id: _,
                            fields,
                            bytes: _,
                        } => Rc::clone(&fields.get(s).expect("Invalid stuct field").typ),
                        _ => panic!("Predecessor type should be struct."),
                    }
                }
            },
            Expr::FuncApp(_) => panic!("Unimplemented!"),
        }
    }
}
