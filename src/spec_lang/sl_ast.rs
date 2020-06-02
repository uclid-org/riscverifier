use std::collections::HashSet;

#[derive(Debug, Clone)]
pub enum BExpr {
    Bool(bool),
    // Boolean operator application
    BOpApp(BoolOp, Vec<Box<BExpr>>),
    // Comparison operator application
    COpApp(CompOp, Vec<Box<VExpr>>),
}

#[derive(Debug, Clone)]
pub enum BoolOp {
    Conj,    // &&
    Disj,    // ||
    Neg,     // !
    Implies, // ==>
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

#[derive(Debug, Clone)]
pub enum VExpr {
    Bv { value: u64, width: u16 },
    Int(i64),
    Bool(bool),
    Var(String),
    OpApp(ValueOp, Vec<Box<VExpr>>),
    FuncApp(String, Vec<Box<VExpr>>),
}

#[derive(Debug, Clone)]
pub enum ValueOp {
    Add,        // +
    Sub,        // -
    Div,        // /
    Mul,        // *
    ArrayIndex, // a[i]
    GetField,   // s.f
    Slice,      // a[lo:hi]
}

#[derive(Debug, Clone)]
pub enum Spec {
    Requires(Box<BExpr>),
    Ensures(Box<BExpr>),
    Modifies(HashSet<String>),
    Track(String, Box<VExpr>),
}

#[derive(Debug, Clone)]
pub struct FuncSpec {
    pub fname: String,
    pub specs: Vec<Box<Spec>>,
}
