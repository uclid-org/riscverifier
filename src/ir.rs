use std::cmp::Ordering;
use std::collections::HashSet;
use std::fmt;
use std::marker::PhantomData;
use std::rc::Rc;

use crate::utils;

/// Types
#[derive(Debug, PartialEq, Eq, Hash)]
pub enum Type {
    Bool,
    Bv {
        w: u64,
    },
    Array {
        in_typs: Vec<Rc<Type>>,
        out_typ: Rc<Type>,
    },
}

#[derive(Debug)]
pub enum Expr {
    Literal(Literal),
    Var(Var),
    Const(Var),
    OpApp(OpApp),
    FuncApp(FuncApp),
}
impl Expr {
    pub fn get_expect_var(&self) -> &Var {
        match self {
            Expr::Var(v) | Expr::Const(v) => v,
            _ => panic!("Not a literal"),
        }
    }
}

/// Literals
#[derive(Debug)]
pub enum Literal {
    Bv { val: u64, width: u64 },
    Bool { val: bool },
}
impl Literal {
    pub fn bv(val: u64, width: u64) -> Self {
        Literal::Bv { val, width }
    }
    pub fn bool(val: bool) -> Self {
        Literal::Bool { val }
    }
}

#[derive(Debug, Eq, Hash, Clone)]
pub struct Var {
    pub name: String,
    pub typ: Rc<Type>,
}
impl Var {
    pub fn new(name: &str, typ: Rc<Type>) -> Self {
        Var {
            name: String::from(name),
            typ: typ,
        }
    }
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
#[derive(Debug)]
pub struct OpApp {
    pub op: Op,
    pub operands: Vec<Rc<Expr>>,
}

/// Operators
#[derive(Debug)]
pub enum Op {
    Comp(CompOp),
    Bv(BVOp),
    Bool(BoolOp),
    ArrayIndex,
}

/// Comparison operators
#[derive(Debug)]
pub enum CompOp {
    Equality,
    Inequality,
}

/// BV operators
#[derive(Debug)]
pub enum BVOp {
    Lt,  // <
    Le,  // <=
    Gt,  // >
    Ge,  // >=
    Ltu, // <_u (unsigned)
    Leu, // <=_u
    Gtu, // >_u
    Geu, // >=_u
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
}

/// Boolean operators
#[derive(Debug)]
pub enum BoolOp {
    Conj, // and: &&
    Disj, // or: ||
    Iff,  // if and only if: <==>
    Impl, // implication: ==>
    Neg,  // negation: !
}

/// Function application
#[derive(Debug)]
pub struct FuncApp {
    pub func_name: &'static str,
    pub operands: Vec<Rc<Expr>>,
}

/// Statements
#[derive(Debug)]
pub enum Stmt {
    Skip,
    Assert(Expr),
    Assume(Expr),
    Havoc(Rc<Var>),
    FuncCall(FuncCall),
    Assign(Assign),
    IfThenElse(IfThenElse),
    Block(Vec<Rc<Stmt>>),
}
impl Stmt {
    pub fn get_expect_block(&self) -> &Vec<Rc<Stmt>> {
        match self {
            Stmt::Block(b) => b,
            _ => panic!("Not a block."),
        }
    }
}

/// Function call statement
#[derive(Debug)]
pub struct FuncCall {
    pub func_name: String,
    pub lhs: Vec<Rc<Expr>>,
    pub operands: Vec<Rc<Expr>>,
}

/// Assign statement
#[derive(Debug)]
pub struct Assign {
    pub lhs: Vec<Rc<Expr>>,
    pub rhs: Vec<Rc<Expr>>,
}

/// If then else statement
#[derive(Debug)]
pub struct IfThenElse {
    pub cond: Box<Expr>,
    pub then_stmt: Box<Stmt>,
    pub else_stmt: Box<Stmt>,
}

/// Verification model datatypes
#[derive(Debug)]
pub struct FuncModel {
    pub sig: FuncSig,
    pub body: Stmt,
    pub inline: bool,
}
impl FuncModel {
    pub fn new(
        name: &str,
        arg_decls: Vec<Expr>,
        ret_decl: Option<Expr>,
        requires: Vec<Expr>,
        ensures: Vec<Expr>,
        body: Stmt,
        inline: bool,
    ) -> Self {
        assert!(
            utils::is_block(&body),
            format!("Body of {} should be a block.", name)
        );
        FuncModel {
            sig: FuncSig::new(name, arg_decls, ret_decl, requires, ensures),
            body: body,
            inline: inline,
        }
    }
}

#[derive(Debug)]
pub struct FuncSig {
    pub name: String,
    pub arg_decls: Vec<Expr>,
    pub ret_decl: Option<Expr>,
    pub requires: Vec<Expr>,
    pub ensures: Vec<Expr>,
}
impl FuncSig {
    pub fn new(
        name: &str,
        arg_decls: Vec<Expr>,
        ret_decl: Option<Expr>,
        requires: Vec<Expr>,
        ensures: Vec<Expr>,
    ) -> Self {
        assert!(
            arg_decls.iter().all(|v| utils::is_var(v)),
            format!("An argument of {} is not a variable.", name)
        );
        if let Some(rd) = &ret_decl {
            assert!(
                utils::is_var(rd),
                format!("The return value of {} is {:?}; not a variable.", name, rd)
            );
        }
        FuncSig {
            name: String::from(name),
            arg_decls,
            ret_decl,
            requires,
            ensures,
        }
    }
}

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
    // fn model_to_string(&self) -> String {}
}

pub trait IRInterface: fmt::Debug {
    /// Expressions to string functions
    fn expr_to_string(expr: &Expr) -> String {
        match expr {
            Expr::Literal(l) => Self::lit_to_string(l),
            Expr::FuncApp(fapp) => Self::fapp_to_string(fapp),
            Expr::OpApp(opapp) => Self::opapp_to_string(opapp),
            Expr::Var(v) | Expr::Const(v) => Self::var_to_string(v),
            _ => panic!("[expr_to_string] Unimplemented."),
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
            Op::Comp(cop) => Self::comp_app_to_string(cop, e1_str, e2_str),
            Op::Bv(bvop) => Self::bv_app_to_string(bvop, e1_str, e2_str),
            Op::Bool(bop) => Self::bool_app_to_string(bop, e1_str, e2_str),
            Op::ArrayIndex => Self::array_index_to_string(e1_str.unwrap(), e2_str.unwrap()),
        }
    }
    fn fapp_to_string(fapp: &FuncApp) -> String;
    fn var_to_string(v: &Var) -> String {
        v.name.clone()
    }
    fn lit_to_string(lit: &Literal) -> String;
    fn typ_to_string(typ: &Type) -> String;
    fn comp_app_to_string(compop: &CompOp, e1: Option<String>, e2: Option<String>) -> String;
    fn bv_app_to_string(bvop: &BVOp, e1: Option<String>, e2: Option<String>) -> String;
    fn bool_app_to_string(bop: &BoolOp, e1: Option<String>, e2: Option<String>) -> String;
    fn array_index_to_string(e1: String, e2: String) -> String;
    /// Statements to string
    fn stmt_to_string(stmt: &Stmt) -> String;
    fn skip_to_string() -> String;
    fn assert_to_string(expr: &Expr) -> String;
    fn assume_to_string(expr: &Expr) -> String;
    fn havoc_to_string(var: &Rc<Var>) -> String;
    fn func_call_to_string(func_call: &FuncCall) -> String;
    fn assign_to_string(assign: &Assign) -> String;
    fn ite_to_string(ite: &IfThenElse) -> String;
    fn block_to_string(blk: &Vec<Rc<Stmt>>) -> String;
    fn func_model_to_string(fm: &FuncModel) -> String;

    // IR to model string
    fn ir_model_to_string(model: &Model) -> String;
}
