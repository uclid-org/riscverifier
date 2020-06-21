use std::{
    cell::RefCell,
    collections::{HashMap, HashSet},
};

use crate::ast;

// ==================================================================
/// # AST Types

#[derive(Debug, Clone, PartialEq)]
pub enum VType {
    Unknown,
    Bv(u16),
    Int,
    Bool,
    Array {
        in_type: Box<VType>,
        out_type: Box<VType>,
    },
    Struct {
        id: String,
        fields: HashMap<String, Box<VType>>,
        size: u64,
    },
}
impl VType {
    /// Returns the width of the type
    pub fn get_bv_width(&self) -> u16 {
        match self {
            Self::Bv(width) => *width,
            _ => panic!("Not a bv type: {:#?}", self),
        }
    }
    /// Infer the operator type based on the `ValueOp` and operands `exprs`
    pub fn infer_op_type(op: &ValueOp, exprs: &Vec<VExpr>) -> VType {
        if exprs.len() == 0 {
            panic!("Operator with no arguments provided.");
        }
        match op {
            ValueOp::ArrayIndex => match exprs[0].typ() {
                Self::Array {
                    in_type: _,
                    out_type,
                } => *out_type.clone(),
                _ => panic!("ArrayIndex should have an array typed first argument."),
            },
            ValueOp::Slice { lo, hi } => Self::Bv(hi - lo),
            ValueOp::GetField => match &exprs[0].typ() {
                Self::Struct {
                    id,
                    fields,
                    size: _,
                } => match &exprs[1] {
                    VExpr::Ident(name, _) => {
                        if let Some(box_typ) = fields.get(name) {
                            *box_typ.clone()
                        } else {
                            panic!("Invalid struct field: {} is not a field of {}.", name, id)
                        }
                    }
                    _ => panic!("Field of GetField operator should be an identifier."),
                },
                _ => panic!("GetField should have a struct typed first argument."),
            },
            ValueOp::Add
            | ValueOp::Sub
            | ValueOp::Div
            | ValueOp::Mul
            | ValueOp::BvXor
            | ValueOp::BvOr
            | ValueOp::BvAnd
            | ValueOp::Deref => {
                // These operators require all the same types
                let same_types = exprs
                    .iter()
                    .fold(true, |acc, expr| acc && exprs[0].typ() == expr.typ());
                if same_types {
                    exprs[0].typ().clone()
                } else {
                    panic!("Expected the same types. {:?}", exprs)
                }
            }
            ValueOp::Concat => {
                let width0 = exprs[0].typ().get_bv_width();
                let width1 = exprs[1].typ().get_bv_width();
                Self::Bv(width0 + width1)
            }
            ValueOp::RightShift | ValueOp::URightShift | ValueOp::LeftShift => {
                exprs[1].typ().clone()
            }
        }
    }
    pub fn infer_func_app_type(fapp: &str, exprs: &Vec<VExpr>) -> VType {
        if exprs.len() == 0 {
            panic!("Function application with no arguments provided.");
        }
        match fapp {
            "old" | "value" => exprs[0].typ().clone(),
            "sext" | "uext" => {
                let expr_width = exprs[1].typ().get_bv_width();
                let ext_width = exprs[0].get_int_value() as u16;
                Self::Bv(expr_width + ext_width)
            }
            _ => panic!("Unimplemented type inference for {}.", fapp),
        }
    }

    /// TODO: Replace this and above with generic and have each AST type implement a type trait
    pub fn from_ast_type(typ: &ast::Type) -> Self {
        match typ {
            ast::Type::Unknown => Self::Unknown,
            ast::Type::Bool => Self::Bool,
            ast::Type::Int => Self::Int,
            ast::Type::Bv { w } => Self::Bv(*w as u16),
            ast::Type::Array { in_typs, out_typ } => {
                let in_type = Box::new(Self::from_ast_type(&in_typs[0]));
                let out_type = Box::new(Self::from_ast_type(&out_typ));
                Self::Array { in_type, out_type }
            }
            ast::Type::Struct { id, fields, w } => {
                let id = id.clone();
                let fields = fields
                    .iter()
                    .map(|kv| {
                        let field_name = (&*kv.0).clone();
                        let field_type = Self::from_ast_type(&*kv.1);
                        (field_name, Box::new(field_type))
                    })
                    .collect();
                let size = *w;
                Self::Struct { id, fields, size }
            }
        }
    }
}

// ==================================================================
/// # AST Expressions

// Boolean expression
#[derive(Debug, Clone)]
pub enum BExpr {
    Bool(bool),
    // Boolean operator application
    BOpApp(BoolOp, Vec<BExpr>),
    // Comparison operator application
    COpApp(CompOp, Vec<VExpr>),
}

#[derive(Debug, Clone)]
pub enum BoolOp {
    Conj,                 // &&
    Disj,                 // ||
    Neg,                  // !
    Implies,              // ==>
    Forall(VExpr, VType), // forall
    Exists(VExpr, VType), // exists
}

#[derive(Debug, Clone)]
pub enum CompOp {
    Equal,  // ==
    Nequal, // !=
    Gt,     // >
    Lt,     // <
    Gtu,    // >_u
    Ltu,    // <_u
    Geq,    // >=
    Leq,    // <=
    Geu,    // >=_u
    Leu,    // <=_u
}

// Value expression
#[derive(Debug, Clone)]
pub enum VExpr {
    Bv { value: u64, typ: VType },
    Int(i64, VType),
    Bool(bool, VType),
    Ident(String, VType),
    OpApp(ValueOp, Vec<VExpr>, VType),
    FuncApp(String, Vec<VExpr>, VType),
}
impl VExpr {
    /// Returns the type of the value expression
    /// based on the dwarf context
    /// If no dwarf context is provided, types are unknown
    /// for variables and expressions consisting of those variables.
    /// Type inference is currently not implemented except for the
    /// usual bottom up type propagation (e.g. int + int => int).
    pub fn typ(&self) -> &VType {
        match self {
            Self::Bv { value: _, typ }
            | Self::Int(_, typ)
            | Self::Bool(_, typ)
            | Self::Ident(_, typ)
            | Self::OpApp(_, _, typ)
            | Self::FuncApp(_, _, typ) => typ,
        }
    }
    /// Helper function that returns the value of a bitvector VExpr
    pub fn get_int_value(&self) -> i64 {
        match self {
            Self::Int(value, _) => *value,
            _ => panic!("Expected `Self::Bv` but found {:?}.", self),
        }
    }
    /// Helper function that returns the identifier name as a string
    pub fn get_ident_name(&self) -> &str {
        match self {
            Self::Ident(name, _) => name,
            _ => panic!("Expected `Self::Ident` but found {:?}.", self),
        }
    }
}

#[derive(Debug, Clone)]
pub enum ValueOp {
    Add,                        // +
    Sub,                        // -
    Div,                        // /
    Mul,                        // *
    BvXor,                      // ^
    BvOr,                       // |
    BvAnd,                      // &
    RightShift,                 // >>
    URightShift,                // >>>
    LeftShift,                  // <<
    ArrayIndex,                 // a[i]
    GetField,                   // s.f
    Slice { lo: u16, hi: u16 }, // a[lo:hi]
    Concat,
    Deref,
}

#[derive(Debug, Clone)]
pub enum Spec {
    Requires(BExpr),
    Ensures(BExpr),
    Modifies(HashSet<String>),
    Track(String, VExpr),
}
impl Spec {
    pub fn get_bexpr(&self) -> Result<&BExpr, ()> {
        match self {
            Self::Requires(e) => Ok(e),
            Self::Ensures(e) => Ok(e),
            _ => Err(()),
        }
    }
}

#[derive(Debug, Clone)]
pub struct FuncSpec {
    pub fname: String,
    pub specs: Vec<Spec>,
}

// ==================================================================
/// # AST Rewriter

pub trait ASTRewriter<C> {
    // BExpr
    fn rewrite_bexpr(bexpr: &mut BExpr, context: &RefCell<C>) {
        match bexpr {
            BExpr::Bool(b) => Self::rewrite_bexpr_bool(b, context),
            BExpr::BOpApp(bop, exprs) => {
                Self::rewrite_bexpr_boolop(bop, context);
                for bexpr in exprs {
                    Self::rewrite_bexpr(bexpr, context);
                }
            }
            BExpr::COpApp(cop, exprs) => {
                Self::rewrite_bexpr_compop(cop, context);
                for vexpr in exprs {
                    Self::rewrite_vexpr(vexpr, context);
                }
            }
        }
    }
    fn rewrite_bexpr_bool(_b: &mut bool, _context: &RefCell<C>) {}
    fn rewrite_bexpr_boolop(_bop: &mut BoolOp, _context: &RefCell<C>) {}
    fn rewrite_bexpr_compop(_cop: &mut CompOp, _context: &RefCell<C>) {}
    // VExpr
    fn rewrite_vexpr(vexpr: &mut VExpr, context: &RefCell<C>) {
        match vexpr {
            VExpr::Bv { value: _, typ: _ } => {
                Self::rewrite_vexpr_bvvalue(vexpr, context);
            }
            VExpr::Int(_, _) => Self::rewrite_vexpr_int(vexpr, context),
            VExpr::Bool(_, _) => Self::rewrite_vexpr_bool(vexpr, context),
            VExpr::Ident(_, _) => Self::rewrite_vexpr_ident(vexpr, context),
            VExpr::OpApp(_, _, _) => Self::rewrite_vexpr_opapp(vexpr, context),
            VExpr::FuncApp(_, _, _) => Self::rewrite_vexpr_funcapp(vexpr, context),
        }
    }
    fn rewrite_vexprs(exprs: &mut Vec<VExpr>, context: &RefCell<C>) {
        for expr in exprs {
            Self::rewrite_vexpr(expr, context);
        }
    }
    fn rewrite_vexpr_bvvalue(_value: &mut VExpr, _context: &RefCell<C>) {}
    fn rewrite_vexpr_int(_i: &mut VExpr, _context: &RefCell<C>) {}
    fn rewrite_vexpr_bool(_b: &mut VExpr, _context: &RefCell<C>) {}
    fn rewrite_vexpr_ident(_vexpr: &mut VExpr, _context: &RefCell<C>) {}
    fn rewrite_vexpr_opapp(opapp: &mut VExpr, context: &RefCell<C>) {
        match opapp {
            VExpr::OpApp(op, exprs, _) => {
                Self::rewrite_vexpr_valueop(op, context);
                Self::rewrite_vexprs(exprs, context);
            }
            _ => panic!("Implementation error; expected `VExpr::OpApp`."),
        }
    }
    fn rewrite_vexpr_funcapp(funcapp: &mut VExpr, context: &RefCell<C>) {
        match funcapp {
            VExpr::FuncApp(fid, exprs, _) => {
                Self::rewrite_vexpr_funcid(fid, context);
                Self::rewrite_vexprs(exprs, context);
            }
            _ => panic!("Implementation error; expected `VExpr::FuncApp`."),
        }
    }
    fn rewrite_vexpr_valueop(_vop: &mut ValueOp, _context: &RefCell<C>) {}
    fn rewrite_vexpr_funcid(_fid: &mut String, _context: &RefCell<C>) {}
}
