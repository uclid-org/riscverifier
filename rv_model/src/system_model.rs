use std::collections::HashSet;
use asts::veriv_ast::*;

// ========================================================================
/// # Constants

/// ## Size constants
pub const BYTE_SIZE: u64 = 8;   // There are 8 bits in a byte
pub const INST_LENGTH_IN_BYTES: u64 = 4; // Instructions are 4 bytes long

/// ## System variable names
pub const PC_VAR: &'static str = "pc";
pub const RETURNED_FLAG: &'static str = "returned";
pub const MEM_VAR: &'static str = "mem";
pub const PRIV_VAR: &'static str = "current_priv";
pub const A0: &'static str = "a0";
pub const SP: &'static str = "sp";
pub const RA: &'static str = "ra";

// ========================================================================
/// # State variables

/// The program counter (PC) variable
pub fn pc_var(xlen: u64) -> Var {
    Var {
        name: PC_VAR.to_string(),
        typ: pc_type(xlen),
    }
}

/// Helper function that returns the PC expression
pub fn pc_expr(xlen: u64) -> Expr {
    Expr::var(PC_VAR, bv_type(xlen))
}

/// Helper function that returns the PC type
pub fn pc_type(xlen: u64) -> Type {
    bv_type(xlen)
}

/// Returned flag that indicates if jalr has been called.
/// TODO(kkmc): We assume all jalr instructions return to
/// the caller, so this flag is set to true in the jalr instruciton.
pub fn returned_var() -> Var {
    Var {
        name: RETURNED_FLAG.to_string(),
        typ: returned_type(),
    }
}

/// Returned flag type
pub fn returned_type() -> Type {
    bv_type(1)
}

/// Memory state variable
pub fn mem_var(xlen: u64) -> Var {
    Var {
        name: MEM_VAR.to_string(),
        typ: mem_type(xlen),
    }
}

/// Helper function that returns the memory expression
pub fn mem_expr(xlen: u64) -> Expr {
    Expr::var(MEM_VAR, mem_type(xlen))
}

/// Returns the type of memory (XLEN addressable byte valued array)
pub fn mem_type(xlen: u64) -> Type {
    Type::Array {
        in_typs: vec![Box::new(bv_type(xlen))],
        out_typ: Box::new(bv_type(BYTE_SIZE)),
    }
}

/// Privilege state variable
pub fn priv_var() -> Var {
    Var {
        name: PRIV_VAR.to_string(),
        typ: priv_type(),
    }
}

/// Helper function that returns the type of privilege
pub fn priv_type() -> Type {
    bv_type(2)
}

/// Returns a bitvector type of specified width
pub fn bv_type(width: u64) -> Type {
    Type::Bv { w: width }
}

/// A set of all the state variables
pub fn sys_state_vars(xlen: u64) -> HashSet<Var> {
    let mut vec_var = HashSet::new();
    vec_var.insert(pc_var(xlen));
    vec_var.insert(returned_var());
    vec_var.insert(mem_var(xlen));
    vec_var.insert(priv_var());
    vec_var
}

// ========================================================================
/// # RISC-V Instruction Semantics

/// ## Helper functions

/// Returns the expression `pc = pc + 4`
pub fn update_pc(xlen: u64) -> Stmt {
    Stmt::assign(
        vec![pc_expr(xlen)],
        vec![Expr::op_app(
            Op::Bv(BVOp::Add),
            vec![pc_expr(xlen), Expr::bv_lit(4, xlen)],
        )],
    )
}

/// Returns the expression `pc = target`
pub fn pc_jump(target: Expr, xlen: u64) -> Stmt {
    Stmt::assign(vec![pc_expr(xlen)], vec![target])
}

/// Unimplemented instruction
/// Use this whenever an instruction is not implemented and you would like to silently pass it
pub fn unimplemented_inst(op: &str, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("unimplemented instruction {}", op)));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// A helper to add nbv64 to the given expression
pub fn add_const(expr: Expr, n: u64, xlen: u64) -> Expr {
    Expr::op_app(Op::Bv(BVOp::Add), vec![expr, Expr::bv_lit(n, xlen)])
} 

/// An expression that returns a byte at the address `addr`
pub fn load_byte(addr: Expr, xlen: u64) -> Expr {
    Expr::op_app(Op::ArrayIndex, vec![mem_expr(xlen), addr])
}

/// An expression that returns a half at the address `addr`
pub fn load_half(addr: Expr, xlen: u64) -> Expr {
    let byte_0 = load_byte(addr.clone(), xlen);
    let byte_1 = load_byte(add_const(addr, 1, xlen), xlen);
    Expr::op_app(Op::Bv(BVOp::Concat), vec![byte_1, byte_0])
}

/// An expression that returns a word at the address `addr`
pub fn load_word(addr: Expr, xlen: u64) -> Expr {
    let half_0 = load_half(addr.clone(), xlen);
    let half_1 = load_half(add_const(addr, 2, xlen), xlen);
    Expr::op_app(Op::Bv(BVOp::Concat), vec![half_1, half_0])
}

/// An expression that returns a double at the address `addr`
pub fn load_double(addr: Expr, xlen: u64) -> Expr {
    let word_0 = load_word(addr.clone(), xlen);
    let word_1 = load_word(add_const(addr, 4, xlen), xlen);
    Expr::op_app(Op::Bv(BVOp::Concat), vec![word_1, word_0])
}

// ========================================================================
/// ## RISC-V Instructions

/// add
pub fn add_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("add {}, {}, {}", rd, rs1, rs2)));
    // rd := rs1 + rs2
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, rs2])],
    ));
    // pc := pc + 4bv64
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sub
pub fn sub_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("sub {}, {}, {}", rd, rs1, rs2)));
    // rd := rs1 - rs2
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::Sub), vec![rs1, rs2])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// mul
pub fn mul_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("mul {}, {}, {}", rd, rs1, rs2)));
    // rd := rs1 * rs2
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::Mul), vec![rs1, rs2])],
    ));
    // pc := pc + 4bv64
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sll
pub fn sll_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("sll {}, {}, {}", rd, rs1, rs2)));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(
            Op::Bv(BVOp::LeftShift),
            vec![
                rs1,
                Expr::op_app(Op::Bv(BVOp::And), vec![rs2, Expr::bv_lit(63, xlen)]),
            ],
        )],
    ));
    // pc := pc + 4bv64
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// slt
pub fn slt_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("slt {}, {}, {}", rd, rs1, rs2)));
    let cond = Expr::op_app(Op::Comp(CompOp::Lt), vec![rs1, rs2]);
    let t_stmt = Stmt::assign(vec![rd.clone()], vec![Expr::bv_lit(1, xlen)]);
    let e_stmt = Stmt::assign(vec![rd.clone()], vec![Expr::bv_lit(0, xlen)]);
    stmts.push(Stmt::if_then_else(
        cond,
        Box::new(t_stmt),
        Some(Box::new(e_stmt)),
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sltu
pub fn sltu_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "sltu {}, {}, {}",
        rd, rs1, rs2
    )));
    let cond = Expr::op_app(Op::Comp(CompOp::Ltu), vec![rs1, rs2]);
    let t_stmt = Stmt::assign(vec![rd.clone()], vec![Expr::bv_lit(1, xlen)]);
    let e_stmt = Stmt::assign(vec![rd.clone()], vec![Expr::bv_lit(0, xlen)]);
    stmts.push(Stmt::if_then_else(
        cond,
        Box::new(t_stmt),
        Some(Box::new(e_stmt)),
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// xor
pub fn xor_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("xor {}, {}, {}", rd, rs1, rs2)));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::Xor), vec![rs1, rs2])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// srl
pub fn srl_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("srl {}, {}, {}", rd, rs1, rs2)));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(
            Op::Bv(BVOp::RightShift),
            vec![
                rs1,
                Expr::op_app(Op::Bv(BVOp::And), vec![rs2, Expr::bv_lit(63, xlen)]),
            ],
        )],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sra
pub fn sra_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("sra {}, {}, {}", rd, rs1, rs2)));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(
            Op::Bv(BVOp::ARightShift),
            vec![
                rs1,
                Expr::op_app(Op::Bv(BVOp::And), vec![rs2, Expr::bv_lit(63, xlen)]),
            ],
        )],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// or
pub fn or_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("or {}, {}, {}", rd, rs1, rs2)));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::Or), vec![rs1, rs2])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// and
pub fn and_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("and {}, {}, {}", rd, rs1, rs2)));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::And), vec![rs1, rs2])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// addw
pub fn addw_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "addw {}, {}, {}",
        rd, rs1, rs2
    )));
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            Expr::op_app(
                Op::Bv(BVOp::Slice { l: 31, r: 0 }),
                vec![Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, rs2])],
            ),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// subw
pub fn subw_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "subw {}, {}, {}",
        rd, rs1, rs2
    )));
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            Expr::op_app(
                Op::Bv(BVOp::Slice { l: 31, r: 0 }),
                vec![Expr::op_app(Op::Bv(BVOp::Sub), vec![rs1, rs2])],
            ),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sllw
pub fn sllw_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "sllw {}, {}, {}",
        rd, rs1, rs2
    )));
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            Expr::op_app(
                Op::Bv(BVOp::LeftShift),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Slice { l: 31, r: 0 }), vec![rs1]),
                    Expr::op_app(
                        Op::Bv(BVOp::Slice { l: 31, r: 0 }),
                        vec![Expr::op_app(
                            Op::Bv(BVOp::And),
                            vec![rs2, Expr::bv_lit(31, xlen)],
                        )],
                    ),
                ],
            ),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// srlw
pub fn srlw_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "srlw {}, {}, {}",
        rd, rs1, rs2
    )));
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            Expr::op_app(
                Op::Bv(BVOp::RightShift),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Slice { l: 31, r: 0 }), vec![rs1]),
                    Expr::op_app(Op::Bv(BVOp::And), vec![rs2, Expr::bv_lit(31, xlen)]),
                ],
            ),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sraw
pub fn sraw_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "sraw {}, {}, {}",
        rd, rs1, rs2
    )));
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            Expr::op_app(
                Op::Bv(BVOp::ARightShift),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Slice { l: 31, r: 0 }), vec![rs1]),
                    Expr::op_app(Op::Bv(BVOp::And), vec![rs2, Expr::bv_lit(31, xlen)]),
                ],
            ),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// jalr
pub fn jalr_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "jalr {}, {}, {}",
        rd, rs1, imm
    )));
    // rd := pc + 4bv64
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(
            Op::Bv(BVOp::Add),
            vec![pc_expr(xlen), Expr::bv_lit(4, xlen)],
        )],
    ));
    let target = Expr::op_app(
        Op::Bv(BVOp::Concat),
        vec![
            Expr::op_app(
                Op::Bv(BVOp::Slice { l: 63, r: 1 }),
                vec![Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, imm])],
            ),
            Expr::bv_lit(0, 1),
        ],
    );
    // pc := (rs1 + imm)[63:1] ++ 0bv1
    stmts.push(pc_jump(target, xlen));
    // returned := 1bv1 (true)
    stmts.push(Stmt::assign(
        vec![Expr::var(RETURNED_FLAG, bv_type(1))],
        vec![Expr::bv_lit(1, 1)],
    ));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// lb
pub fn lb_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("lb {}, {}, {}", rd, rs1, imm)));
    let addr = Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, imm]);
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            load_byte(addr, xlen),
            Expr::int_lit(56),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// lh
pub fn lh_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("lh {}, {}, {}", rd, rs1, imm)));
    let addr = Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, imm]);
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            load_half(addr, xlen),
            Expr::int_lit(48),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// lw
pub fn lw_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("lw {}, {}, {}", rd, rs1, imm)));
    let addr = Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, imm]);
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            load_word(addr, xlen),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// lbu
/// FIXME
pub fn lbu_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("lbu {}, {}, {}", rd, rs1, imm)));
    let addr = Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, imm]);
    let ret = Expr::op_app(
        Op::Bv(BVOp::ZeroExt),
        vec![
            load_byte(addr, xlen),
            Expr::int_lit(56),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// lhu
/// FIXME
pub fn lhu_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("lhu {}, {}, {}", rd, rs1, imm)));
    let addr = Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, imm]);
    let ret = Expr::op_app(
        Op::Bv(BVOp::ZeroExt),
        vec![
            load_half(addr, xlen),
            Expr::int_lit(48),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// addi
/// FIXME
pub fn addi_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "addi {}, {}, {}",
        rd, rs1, imm
    )));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, imm])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// slti
pub fn slti_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "slti {}, {}, {}",
        rd, rs1, imm
    )));
    let cond = Expr::op_app(Op::Comp(CompOp::Lt), vec![rs1, imm]);
    let t_stmt = Stmt::assign(vec![rd.clone()], vec![Expr::bv_lit(1, xlen)]);
    let e_stmt = Stmt::assign(vec![rd.clone()], vec![Expr::bv_lit(0, xlen)]);
    stmts.push(Stmt::if_then_else(
        cond,
        Box::new(t_stmt),
        Some(Box::new(e_stmt)),
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sltiu
pub fn sltiu_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "sltiu {}, {}, {}",
        rd, rs1, imm
    )));
    let cond = Expr::op_app(Op::Comp(CompOp::Ltu), vec![rs1, imm]);
    let t_stmt = Stmt::assign(vec![rd.clone()], vec![Expr::bv_lit(1, xlen)]);
    let e_stmt = Stmt::assign(vec![rd.clone()], vec![Expr::bv_lit(0, xlen)]);
    stmts.push(Stmt::if_then_else(
        cond,
        Box::new(t_stmt),
        Some(Box::new(e_stmt)),
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// xori
/// FIXME
pub fn xori_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "xori {}, {}, {}",
        rd, rs1, rs2
    )));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::Xor), vec![rs1, rs2])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// ori
/// FIXME
pub fn ori_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("ori {}, {}, {}", rd, rs1, rs2)));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::Or), vec![rs1, rs2])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// andi
/// FIXME
pub fn andi_inst(rd: Expr, rs1: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "andi {}, {}, {}",
        rd, rs1, rs2
    )));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::And), vec![rs1, rs2])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// slli
pub fn slli_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "slli {}, {}, {}",
        rd, rs1, imm
    )));
    stmts.push(Stmt::Assume(Expr::op_app(
        Op::Comp(CompOp::Ltu),
        vec![imm.clone(), Expr::bv_lit(64, xlen)],
    )));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::LeftShift), vec![rs1, imm])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// srli
pub fn srli_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "srli {}, {}, {}",
        rd, rs1, imm
    )));
    stmts.push(Stmt::Assume(Expr::op_app(
        Op::Comp(CompOp::Ltu),
        vec![imm.clone(), Expr::bv_lit(64, xlen)],
    )));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::RightShift), vec![rs1, imm])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// srai
pub fn srai_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "srai {}, {}, {}",
        rd, rs1, imm
    )));
    stmts.push(Stmt::Assume(Expr::op_app(
        Op::Comp(CompOp::Ltu),
        vec![imm.clone(), Expr::bv_lit(64, xlen)],
    )));
    stmts.push(Stmt::assign(
        vec![rd],
        vec![Expr::op_app(Op::Bv(BVOp::ARightShift), vec![rs1, imm])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// lwu
pub fn lwu_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("lwu {}, {}, {}", rd, rs1, imm)));
    let addr = Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, imm]);
    let ret = Expr::op_app(
        Op::Bv(BVOp::ZeroExt),
        vec![
            load_word(addr, xlen),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// ld
pub fn ld_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("ld {}, {}, {}", rd, rs1, imm)));
    let addr = Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, imm]);
    let ret = load_double(addr, xlen);
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// addiw
pub fn addiw_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "addiw {}, {}, {}",
        rd, rs1, imm
    )));
    let rs1_sliced = Expr::op_app(Op::Bv(BVOp::Slice { l: 31, r: 0 }), vec![rs1]);
    let imm_sliced = Expr::op_app(Op::Bv(BVOp::Slice { l: 31, r: 0 }), vec![imm]);
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            Expr::op_app(
                Op::Bv(BVOp::Slice { l: 31, r: 0 }),
                vec![Expr::op_app(
                    Op::Bv(BVOp::Add),
                    vec![rs1_sliced, imm_sliced],
                )],
            ),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// slliw
pub fn slliw_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "slliw {}, {}, {}",
        rd, rs1, imm
    )));
    let rs1_sliced = Expr::op_app(Op::Bv(BVOp::Slice { l: 31, r: 0 }), vec![rs1]);
    let imm_sliced = Expr::op_app(Op::Bv(BVOp::Slice { l: 31, r: 0 }), vec![imm]);
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            Expr::op_app(Op::Bv(BVOp::LeftShift), vec![rs1_sliced, imm_sliced]),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// srliw
pub fn srliw_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "srliw {}, {}, {}",
        rd, rs1, imm
    )));
    let rs1_sliced = Expr::op_app(Op::Bv(BVOp::Slice { l: 31, r: 0 }), vec![rs1]);
    let imm_sliced = Expr::op_app(Op::Bv(BVOp::Slice { l: 31, r: 0 }), vec![imm]);
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            Expr::op_app(Op::Bv(BVOp::RightShift), vec![rs1_sliced, imm_sliced]),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sraiw
pub fn sraiw_inst(rd: Expr, rs1: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "sraiw {}, {}, {}",
        rd, rs1, imm
    )));
    let rs1_sliced = Expr::op_app(Op::Bv(BVOp::Slice { l: 31, r: 0 }), vec![rs1]);
    let imm_sliced = Expr::op_app(Op::Bv(BVOp::Slice { l: 31, r: 0 }), vec![imm]);
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            Expr::op_app(Op::Bv(BVOp::ARightShift), vec![rs1_sliced, imm_sliced]),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sb
pub fn sb_inst(rs1: Expr, imm: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("sb {}, {}, {}", rs1, imm, rs2)));
    let mem_addr = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(Op::Bv(BVOp::Add), vec![rs1, imm]),
        ],
    );
    stmts.push(Stmt::assign(
        vec![mem_addr],
        vec![Expr::op_app(Op::Bv(BVOp::Slice { l: 7, r: 0 }), vec![rs2])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sh
pub fn sh_inst(rs1: Expr, imm: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("sh {}, {}, {}", rs1, imm, rs2)));
    let mem_addr = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
        ],
    );
    let mem_addr_1 = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(
                Op::Bv(BVOp::Add),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
                    Expr::bv_lit(1, xlen),
                ],
            ),
        ],
    );
    stmts.push(Stmt::assign(
        vec![mem_addr.clone()],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 7, r: 0 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(Stmt::assign(
        vec![mem_addr_1.clone()],
        vec![Expr::op_app(Op::Bv(BVOp::Slice { l: 15, r: 8 }), vec![rs2])],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sw
pub fn sw_inst(rs1: Expr, imm: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("sw {}, {}, {}", rs1, imm, rs2)));
    let mem_addr = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
        ],
    );
    let mem_addr_1 = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(
                Op::Bv(BVOp::Add),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
                    Expr::bv_lit(1, xlen),
                ],
            ),
        ],
    );
    let mem_addr_2 = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(
                Op::Bv(BVOp::Add),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
                    Expr::bv_lit(2, xlen),
                ],
            ),
        ],
    );
    let mem_addr_3 = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(
                Op::Bv(BVOp::Add),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
                    Expr::bv_lit(3, xlen),
                ],
            ),
        ],
    );
    stmts.push(Stmt::assign(
        vec![mem_addr],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 7, r: 0 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(Stmt::assign(
        vec![mem_addr_1],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 15, r: 8 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(Stmt::assign(
        vec![mem_addr_2],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 23, r: 16 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(Stmt::assign(
        vec![mem_addr_3],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 31, r: 24 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// sd
pub fn sd_inst(rs1: Expr, imm: Expr, rs2: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("sd {}, {}, {}", rs1, imm, rs2)));
    let mem_addr = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
        ],
    );
    let mem_addr_1 = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(
                Op::Bv(BVOp::Add),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
                    Expr::bv_lit(1, xlen),
                ],
            ),
        ],
    );
    let mem_addr_2 = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(
                Op::Bv(BVOp::Add),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
                    Expr::bv_lit(2, xlen),
                ],
            ),
        ],
    );
    let mem_addr_3 = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(
                Op::Bv(BVOp::Add),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
                    Expr::bv_lit(3, xlen),
                ],
            ),
        ],
    );
    let mem_addr_4 = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(
                Op::Bv(BVOp::Add),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
                    Expr::bv_lit(4, xlen),
                ],
            ),
        ],
    );
    let mem_addr_5 = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(
                Op::Bv(BVOp::Add),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
                    Expr::bv_lit(5, xlen),
                ],
            ),
        ],
    );
    let mem_addr_6 = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(
                Op::Bv(BVOp::Add),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
                    Expr::bv_lit(6, xlen),
                ],
            ),
        ],
    );
    let mem_addr_7 = Expr::op_app(
        Op::ArrayIndex,
        vec![
            mem_expr(xlen),
            Expr::op_app(
                Op::Bv(BVOp::Add),
                vec![
                    Expr::op_app(Op::Bv(BVOp::Add), vec![rs1.clone(), imm.clone()]),
                    Expr::bv_lit(7, xlen),
                ],
            ),
        ],
    );
    stmts.push(Stmt::assign(
        vec![mem_addr],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 7, r: 0 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(Stmt::assign(
        vec![mem_addr_1],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 15, r: 8 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(Stmt::assign(
        vec![mem_addr_2],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 23, r: 16 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(Stmt::assign(
        vec![mem_addr_3],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 31, r: 24 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(Stmt::assign(
        vec![mem_addr_4],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 39, r: 32 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(Stmt::assign(
        vec![mem_addr_5],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 47, r: 40 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(Stmt::assign(
        vec![mem_addr_6],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 55, r: 48 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(Stmt::assign(
        vec![mem_addr_7],
        vec![Expr::op_app(
            Op::Bv(BVOp::Slice { l: 63, r: 56 }),
            vec![rs2.clone()],
        )],
    ));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// beq
pub fn beq_inst(rs1: Expr, rs2: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "beq {}, {}, {}",
        rs1, rs2, imm
    )));
    let cond = Expr::op_app(Op::Comp(CompOp::Equality), vec![rs1, rs2]);
    let t_stmt = pc_jump(imm, xlen);
    let e_stmt = update_pc(xlen);
    stmts.push(Stmt::if_then_else(
        cond,
        Box::new(t_stmt),
        Some(Box::new(e_stmt)),
    ));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// bne
pub fn bne_inst(rs1: Expr, rs2: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "bne {}, {}, {}",
        rs1, rs2, imm
    )));
    let cond = Expr::op_app(Op::Comp(CompOp::Inequality), vec![rs1, rs2]);
    let t_stmt = pc_jump(imm, xlen);
    let e_stmt = update_pc(xlen);
    stmts.push(Stmt::if_then_else(
        cond,
        Box::new(t_stmt),
        Some(Box::new(e_stmt)),
    ));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// blt
pub fn blt_inst(rs1: Expr, rs2: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "blt {}, {}, {}",
        rs1, rs2, imm
    )));
    let cond = Expr::op_app(Op::Comp(CompOp::Lt), vec![rs1, rs2]);
    let t_stmt = pc_jump(imm, xlen);
    let e_stmt = update_pc(xlen);
    stmts.push(Stmt::if_then_else(
        cond,
        Box::new(t_stmt),
        Some(Box::new(e_stmt)),
    ));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// bge
pub fn bge_inst(rs1: Expr, rs2: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "bge {}, {}, {}",
        rs1, rs2, imm
    )));
    let cond = Expr::op_app(Op::Comp(CompOp::Ge), vec![rs1, rs2]);
    let t_stmt = pc_jump(imm, xlen);
    let e_stmt = update_pc(xlen);
    stmts.push(Stmt::if_then_else(
        cond,
        Box::new(t_stmt),
        Some(Box::new(e_stmt)),
    ));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// bltu
pub fn bltu_inst(rs1: Expr, rs2: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "bltu {}, {}, {}",
        rs1, rs2, imm
    )));
    let cond = Expr::op_app(Op::Comp(CompOp::Ltu), vec![rs1, rs2]);
    let t_stmt = pc_jump(imm, xlen);
    let e_stmt = update_pc(xlen);
    stmts.push(Stmt::if_then_else(
        cond,
        Box::new(t_stmt),
        Some(Box::new(e_stmt)),
    ));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// bgeu
pub fn bgeu_inst(rs1: Expr, rs2: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!(
        "bgeu {}, {}, {}",
        rs1, rs2, imm
    )));
    let cond = Expr::op_app(Op::Comp(CompOp::Geu), vec![rs1, rs2]);
    let t_stmt = pc_jump(imm, xlen);
    let e_stmt = update_pc(xlen);
    stmts.push(Stmt::if_then_else(
        cond,
        Box::new(t_stmt),
        Some(Box::new(e_stmt)),
    ));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// lui
pub fn lui_inst(rd: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("lui {}, {}", rd, imm)));
    let ret = Expr::op_app(
        Op::Bv(BVOp::SignExt),
        vec![
            Expr::op_app(
                Op::Bv(BVOp::LeftShift),
                vec![
                    Expr::op_app(
                        Op::Bv(BVOp::ZeroExt),
                        vec![
                            Expr::op_app(Op::Bv(BVOp::Slice { l: 19, r: 0 }), vec![imm]),
                            Expr::int_lit(12),
                        ],
                    ),
                    Expr::bv_lit(12, 32),
                ],
            ),
            Expr::int_lit(32),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// auipc
pub fn auipc_inst(rd: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("auipc {}, {}", rd, imm)));
    let ret = Expr::op_app(
        Op::Bv(BVOp::Add),
        vec![
            pc_expr(xlen),
            Expr::op_app(Op::Bv(BVOp::LeftShift), vec![imm, Expr::bv_lit(12, xlen)]),
        ],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(update_pc(xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

/// jal
pub fn jal_inst(rd: Expr, imm: Expr, xlen: u64) -> Stmt {
    let mut stmts = vec![];
    stmts.push(Stmt::Comment(format!("jal {}, {}", rd, imm)));
    let ret = Expr::op_app(
        Op::Bv(BVOp::Add),
        vec![pc_expr(xlen), Expr::bv_lit(4, xlen)],
    );
    stmts.push(Stmt::assign(vec![rd], vec![ret]));
    stmts.push(pc_jump(imm, xlen));
    Stmt::Block(stmts.iter().map(|x| Box::new(x.clone())).collect())
}

// TODO(kkmc): IMPLEMENT CSR INSTRUCTIONS
