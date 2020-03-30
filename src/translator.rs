use std::boxed::Box;
use std::collections::HashMap;
use std::collections::HashSet;
use std::marker::PhantomData;
use std::rc::Rc;

use topological_sort::TopologicalSort;

use crate::ir::*;
use crate::readers::dwarfreader::{DwarfCtx, DwarfTypeDefn};
use crate::readers::objectdumpreader::*;
use crate::set;
use crate::utils;

/// ========== Constants ==========================================
pub const PC_VAR: &str = "pc";
pub const MEM_VAR: &str = "mem";
pub const PRIV_VAR: &str = "current_priv";
pub const EXCEPT_VAR: &str = "exception";

/// ========== Translator ==========================================
/// Instruction level translator from RISC-V to verification IR
pub struct Translator<'t, I>
where
    I: IRInterface,
{
    /// Width of integer register in bits (FIXME: also currently used for address length)
    xlen: u64,
    /// Verification model
    model: Model,
    /// Map of function names to thier CFGs
    func_cfg_map: &'t HashMap<String, Rc<Cfg>>,
    /// A set that memoizes all the functions already generated
    generated_funcs: HashSet<String>,
    /// A set of the functions to ignore
    ignored_funcs: &'t HashSet<&'t str>,
    /// Map of procedure name to thier modifies set
    mod_set_map: HashMap<String, HashSet<String>>,
    /// DWARF debugging information
    dwarf_ctx: &'t DwarfCtx,
    /// Map of specs from function name to a list of pre/post conditions
    specs_map: &'t HashMap<String, Vec<Spec>>,
    /// Don't touch this
    _phantom_i: PhantomData<I>,
}
impl<'t, I> Translator<'t, I>
where
    I: IRInterface,
{
    /// Translator constructor
    pub fn new(
        xlen: u64,
        module_name: &'t str,
        func_cfg_map: &'t HashMap<String, Rc<Cfg>>,
        ignored_funcs: &'t HashSet<&'t str>,
        dwarf_ctx: &'t DwarfCtx,
        specs_map: &'t HashMap<String, Vec<Spec>>,
    ) -> Self {
        Translator {
            xlen,
            model: Model::new(module_name),
            func_cfg_map,
            generated_funcs: HashSet::new(),
            ignored_funcs,
            mod_set_map: HashMap::new(),
            dwarf_ctx,
            specs_map,
            _phantom_i: PhantomData,
        }
    }
    /// Outputs the model into output stream
    pub fn print_model(&self) {
        println!(
            "{}",
            I::model_to_string(&self.xlen, &self.model, &self.dwarf_ctx)
        );
    }
    /// Generates a stub function with the specifications provided
    pub fn gen_func_model_stub(&mut self, func_name: &str) -> Result<(), utils::Error> {
        // Get the arguments
        let arg_decls = self.func_args(func_name);
        // Translate the specification
        let mod_set = self.mod_set_from_spec_map(func_name).map_or_else(
            || Some(set![String::from(PC_VAR)]),
            |mut s| {
                s.insert(String::from(PC_VAR));
                Some(s)
            },
        );
        if let Some(ms) = &mod_set {
            self.mod_set_map.insert(func_name.to_string(), ms.clone());
        }
        let requires = self.requires_from_spec_map(func_name, &arg_decls).ok();
        let ensures = self.ensures_from_spec_map(func_name).map_or_else(
            || Some(vec![self.pc_eventually_ra_spec()]),
            |mut v| {
                v.push(self.pc_eventually_ra_spec());
                Some(v)
            },
        );
        let ret_decl = None;
        // Create stub function model
        let stub_fm = FuncModel::new(
            func_name,
            *self.get_func_entry_addr(func_name)?,
            arg_decls,
            ret_decl,
            requires,
            ensures,
            mod_set,
            Stmt::Block(vec![]),
            false,
        );
        self.model.add_func_model(stub_fm);
        Ok(())
    }
    /// Generates a model for the function named "func_name"
    pub fn gen_func_model(&mut self, func_name: &str) -> Result<(), utils::Error> {
        if self.ignored_funcs.get(func_name).is_some() {
            self.gen_func_model_stub(func_name)?;
            return Ok(());
        }
        if self.generated_funcs.get(func_name).is_some() {
            return Ok(());
        }
        self.generated_funcs.insert(func_name.to_string());
        // Add global variables for the function block
        self.model
            .add_vars(&self.infer_vars(self.get_func_cfg(func_name)?));
        // Add system global variables
        self.model.add_vars(&self.sys_state_vars());
        // Generate procedure model for each basic block in the function
        let bb_fms = self
            .get_func_cfg(func_name)?
            .bbs()
            .iter()
            .map(|(entry_addr, bb)| {
                let bb_proc_name = self.bb_proc_name(*entry_addr);
                let body = self.bb_to_block(bb);
                let mod_set = self.bb_mod_set(bb);
                FuncModel::new(
                    &bb_proc_name,
                    *entry_addr,
                    vec![],
                    None,
                    None,
                    None,
                    Some(mod_set),
                    body,
                    true,
                )
            })
            .collect::<Vec<_>>();
        // Add all basic block mod sets to the model
        let bb_mod_sets = bb_fms
            .iter()
            .map(|fm| (fm.sig.name.clone(), fm.sig.mod_set.clone()))
            .collect::<Vec<(String, HashSet<String>)>>();
        for bb_mod_set in bb_mod_sets {
            self.mod_set_map.insert(bb_mod_set.0, bb_mod_set.1);
        }
        let callees = self.get_callee_addrs(self.get_func_cfg(func_name)?);
        // Compute modifies set for the current function
        let mut func_mod_set = bb_fms
            .iter()
            .map(|bb_fm| bb_fm.sig.mod_set.clone())
            .flatten()
            .collect::<HashSet<String>>();
        // Add basic blocks to model
        self.model.add_func_models(bb_fms);
        // Depth first recursive call (required
        // to happen before we create the current function
        // because we need to compute the modifies set)
        for callee in &callees {
            assert!(
                self.is_func_entry(&callee.to_string()[..]),
                format!("Address {} was not found or not an entry point.", callee)
            );
            let callee_name = self.get_func_name(callee).unwrap();
            self.gen_func_model(&callee_name[..])?;
        }
        // Add callee mod set variables
        for callee in &callees {
            let callee_name = self.get_func_name(callee).unwrap();
            if self.ignored_funcs.get(&callee_name[..]).is_some() {
                continue;
            }
            func_mod_set = func_mod_set
                .union(self.mod_set_map.get(&callee_name).unwrap())
                .cloned()
                .collect::<HashSet<String>>();
        }
        // Memoize modifies set for the current function
        self.mod_set_map
            .insert(func_name.to_string(), func_mod_set.clone());
        // Get the arguments
        let arg_decls = self.func_args(func_name);
        // Translate the specification
        let requires = self.requires_from_spec_map(func_name, &arg_decls).ok();
        let ensures = self.ensures_from_spec_map(func_name);
        let ret_decl = None;
        // Create the cfg
        let body = self.gen_func_body(&Rc::clone(self.get_func_cfg(func_name)?));
        let real_mod_set = self.infer_mod_set(&body);
        self.mod_set_map
            .insert(func_name.to_string(), real_mod_set.clone());
        // Add function model
        self.model.add_func_model(FuncModel::new(
            func_name,
            *self.get_func_entry_addr(func_name)?,
            arg_decls,
            ret_decl,
            requires,
            ensures,
            // Some(func_mod_set),
            Some(real_mod_set),
            body,
            true, // FIXME: Inlined for now otherwise we would need a quantifier over the memory
        ));
        Ok(())
    }
    /// Computes the arguments of a function from the DWARF info
    fn func_args(&self, func_name: &str) -> Vec<Expr> {
        self.dwarf_ctx
            .func_sig(func_name)
            .ok()
            .and_then(|fs| {
                Some(
                    fs.args
                        .iter()
                        .map(|x| Expr::var(&x.name[..], self.dwarf_typ_to_ir(&x.typ_defn)))
                        .collect::<Vec<Expr>>(),
                )
            })
            .map_or(vec![], |v| v)
    }
    /// Function model body
    fn gen_func_body(&mut self, cfg: &Rc<Cfg>) -> Stmt {
        let mut stmts_vec = vec![];
        let top_sort = self.topological_sort(&cfg);
        // Add basic blocks in topological order
        let callees = self.get_callee_addrs(&cfg);
        for entry_addr in top_sort {
            // Ignore callee function calls and handle with
            // basic_blk_call (if jump is the last inst of
            // the basic block)
            if callees.get(&entry_addr).is_some() {
                continue;
            } else {
                stmts_vec.push(Box::new(self.basic_blk_call(entry_addr, cfg)));
            }
        }
        Stmt::Block(stmts_vec)
    }
    /// Basic block call in function body
    fn basic_blk_call(&mut self, entry_addr: u64, cfg: &Rc<Cfg>) -> Stmt {
        // Assertion statements after the basic block executes (should only be used when inlining as a sanity check)
        let mut then_stmts_inner = vec![];
        // Add call to basic block
        let call_stmt = Stmt::func_call(self.bb_proc_name(entry_addr), vec![], vec![]);
        then_stmts_inner.push(Box::new(call_stmt));
        // Assert statements for jump targets
        let mut fallthru_guard = None;
        let mut jump_guard = None;
        let mut callee_call = false;
        // Fall through target
        if let Some(target_addr) = cfg.next_blk_addr(entry_addr) {
            fallthru_guard = Some(Expr::op_app(
                Op::Comp(CompOp::Equality),
                vec![
                    Expr::Var(self.pc_var()),
                    Expr::bv_lit(*target_addr, self.xlen),
                ],
            ));
        }
        // Jump target (remove fall through if target is function entry; ie. JAL)
        if let Some(target_addr) = cfg.next_abs_jump_addr(entry_addr) {
            if self.is_func_entry(&target_addr.to_string()[..]) {
                callee_call = true;
            }
            jump_guard = Some(Expr::op_app(
                Op::Comp(CompOp::Equality),
                vec![
                    Expr::Var(self.pc_var()),
                    Expr::bv_lit(*target_addr, self.xlen),
                ],
            ));
        }
        // Add guard for after basic block
        if fallthru_guard.is_some() && jump_guard.is_some() && !callee_call {
            then_stmts_inner.push(Box::new(Stmt::Assert(Expr::op_app(
                Op::Bool(BoolOp::Disj),
                vec![fallthru_guard.clone().unwrap(), jump_guard.clone().unwrap()],
            ))));
        } else if jump_guard.is_some() {
            then_stmts_inner.push(Box::new(Stmt::Assert(jump_guard.clone().unwrap())));
        } else if fallthru_guard.is_some() {
            then_stmts_inner.push(Box::new(Stmt::Assert(fallthru_guard.clone().unwrap())));
        }
        // Add call statement to callee function if the basic block ends in a function call
        if let Some(target_addr) = cfg.next_abs_jump_addr(entry_addr) {
            // Absolute jump to a function entry.
            // In this case, call the function.
            if self.is_func_entry(&target_addr.to_string()[..]) {
                let func_name = self.get_func_name(target_addr).unwrap();
                let args = self
                    .dwarf_ctx
                    // Get the function signature
                    .func_sig(&func_name)
                    .ok()
                    .and_then(|fs| {
                        Some(
                            fs.args
                                .iter()
                                .enumerate()
                                .map(|(i, dwarf_var)| {
                                    // Infer the argument sizes and use the a registers as inputs
                                    let reg_var = Expr::var(&format!("a{}", i), Type::Unknown);
                                    let typ = self.dwarf_typ_to_ir(&dwarf_var.typ_defn);
                                    Expr::op_app(
                                        Op::Bv(BVOp::Slice {
                                            l: typ.get_expect_bv_width() - 1,
                                            r: 0,
                                        }),
                                        vec![reg_var],
                                    )
                                })
                                .collect::<Vec<_>>(),
                        )
                    })
                    .map_or(vec![], |v| v);
                let call_func_stmt = Stmt::func_call(func_name, vec![], args);
                // Add the call statement to the then statement
                then_stmts_inner.push(Box::new(call_func_stmt));
                if let Some(guard) = fallthru_guard {
                    then_stmts_inner.push(Box::new(Stmt::Assert(guard)));
                }
            } else {
                // Absolute jump to a basic block.
                // In this case, recursively build a tree of basic block executions
                let func_cfg = Rc::clone(
                    self.get_func_cfg_addr(&target_addr)
                        .expect(&format!("No CFG found containing address {}.", target_addr)),
                );
                let call_bb_stmt = self.basic_blk_call(*target_addr, &func_cfg);
                then_stmts_inner.push(Box::new(call_bb_stmt));
                // Also generate the function if it's not already generated
                let func_at_target_addr = self.func_at_addr(target_addr).expect(&format!(
                    "Could not find a function defined at {}.",
                    target_addr
                ));
                self.gen_func_model(&func_at_target_addr).expect(&format!(
                    "Unable to generate a function model for function {}.",
                    target_addr
                ));
            }
        }
        let then_stmt = Box::new(Stmt::Block(then_stmts_inner));
        // Add condition that checks if pc == basic block entry address
        let cond = Expr::op_app(
            Op::Comp(CompOp::Equality),
            vec![
                Expr::Var(self.pc_var()),
                Expr::bv_lit(entry_addr, self.xlen),
            ],
        );
        Stmt::if_then_else(cond, then_stmt, None)
    }
    /// Topologically sorted list of entry addresses in the CFG
    fn topological_sort(&self, cfg: &Rc<Cfg>) -> Vec<u64> {
        let mut sorted = vec![];
        let mut ts = TopologicalSort::<&u64>::new();
        ts.insert(cfg.get_entry_addr());
        for (entry_addr, bb) in cfg.bbs() {
            if let Some(jump_target) = cfg.next_abs_jump_addr(*entry_addr) {
                if let Some(target) = cfg.next_blk_addr(*entry_addr) {
                    // FIXME: Check if this is okay for the security monitor. We assume all external jumps will return and have
                    // added asserts to check this in the verification models.
                    // 1. Add fallthrough for all non-jal instructions
                    // 2. Add fallthrough only if a jump instruction doesn't jump to the current function and is an external function call
                    if bb.insts().last().unwrap().base_instruction_name() != "jal"
                        || (self.get_func_name(&jump_target)
                            != self.get_func_name(&cfg.get_entry_addr())
                            && self.is_func_entry(&jump_target.to_string()))
                    {
                        ts.add_dependency(entry_addr, target);
                    }
                }
                ts.add_dependency(entry_addr, jump_target);
            }
        }
        loop {
            let mut v = ts.pop_all();
            if v.is_empty() {
                if ts.len() != 0 {
                    // If ts.pop_all() is empty and len() != 0, there is a cycle
                    let cycle = cfg
                        .find_cycle(&*cfg.get_entry_addr(), &mut HashSet::new(), &mut false)
                        .expect("Should have found a cycle.");
                    panic!(
                        "There is a cycle in the cfg of {:?}: {:?}.",
                        self.get_func_name(&cfg.get_entry_addr()),
                        cycle
                            .iter()
                            .rev()
                            .map(|v| format!("{:#x?}", v))
                            .collect::<Vec<String>>()
                    )
                } else {
                    // Otherwise it's the end of the topological sort
                    break;
                }
            }
            v.sort();
            sorted.extend(v);
        }
        sorted
    }
    /// Translates a basic block object into a statement
    fn bb_to_block(&self, bb: &BasicBlock) -> Stmt {
        let mut inst_vec = vec![];
        for al in bb.insts() {
            inst_vec.push(Box::new(self.al_to_ir(&al)));
        }
        Stmt::Block(inst_vec)
    }
    /// Assembly line to IR
    fn al_to_ir(&self, al: &Rc<AssemblyLine>) -> Stmt {
        let func_name = self.inst_proc_name(al.base_instruction_name());
        // outputs
        let mut lhs = vec![];
        let mut regs: [Option<&InstOperand>; 2] = [al.rd(), al.csr()];
        for reg_op in regs.iter_mut() {
            if let Some(reg) = reg_op {
                lhs.push(Expr::var(&reg.get_reg_name()[..], self.bv_type(self.xlen)));
                assert!(!reg.has_offset());
            }
        }
        // inputs
        let mut operands = vec![];
        let mut regs: [Option<&InstOperand>; 3] = [al.rs1(), al.rs2(), al.csr()];
        for reg_op in regs.iter_mut() {
            if let Some(reg) = reg_op {
                operands.push(Expr::var(&reg.get_reg_name()[..], self.bv_type(self.xlen)));
                if reg.has_offset() {
                    operands.push(Expr::bv_lit(reg.get_reg_offset() as u64, self.xlen));
                }
            }
        }
        // immediate input
        if let Some(imm) = al.imm() {
            operands.push(Expr::bv_lit(imm.get_imm_val() as u64, self.xlen));
        }
        Stmt::func_call(func_name, lhs, operands)
    }
    /// =================== Helper functions ===================
    /// Returns the inferred modifies set
    fn infer_mod_set(&self, stmt: &Stmt) -> HashSet<String> {
        let mut mod_set = HashSet::new();
        mod_set.insert(PC_VAR.to_string());
        mod_set.insert(EXCEPT_VAR.to_string()); // Note: Doesn't always need to be modified
        match stmt {
            Stmt::Havoc(rc_var) => {
                mod_set.insert(rc_var.name.clone());
            }
            Stmt::FuncCall(fc) => {
                let fc_mod_set = self.mod_set_map.get(&fc.func_name).expect(&format!(
                    "Unable to find modifies set for {}.",
                    fc.func_name
                ));
                mod_set = mod_set.union(&fc_mod_set).cloned().collect();
            }
            Stmt::Assign(a) => {
                let lhs_mod_set = a
                    .lhs
                    .iter()
                    .map(|e| e.get_expect_var().name.clone())
                    .collect::<HashSet<String>>();
                mod_set = mod_set.union(&lhs_mod_set).cloned().collect();
            }
            Stmt::IfThenElse(ite) => {
                let then_mod_set = self.infer_mod_set(&ite.then_stmt);
                mod_set = mod_set.union(&then_mod_set).cloned().collect();
                if let Some(else_stmt) = &ite.else_stmt {
                    let else_mod_set = self.infer_mod_set(else_stmt);
                    mod_set = mod_set.union(&else_mod_set).cloned().collect();
                }
            }
            Stmt::Block(blk) => {
                let blk_mod_sets = blk
                    .iter()
                    .map(|stmt| self.infer_mod_set(stmt))
                    .flatten()
                    .collect::<HashSet<String>>();
                mod_set = mod_set.union(&blk_mod_sets).cloned().collect();
            }
            _ => (),
        }
        mod_set
    }
    /// Compute modifies set for a basic block
    fn bb_mod_set(&self, bb: &BasicBlock) -> HashSet<String> {
        let mut mod_set = HashSet::new();
        mod_set.insert(PC_VAR.to_string());
        mod_set.insert(EXCEPT_VAR.to_string()); // Note: Doesn't always need to be modified
        for al in bb.insts() {
            if let Some(reg) = al.rd() {
                mod_set.insert(reg.get_reg_name());
            }
            if let Some(reg) = al.csr() {
                mod_set.insert(reg.get_reg_name());
            }
            match al.base_instruction_name() {
                "sb" | "sh" | "sw" | "sd" => mod_set.insert(MEM_VAR.to_string()),
                _ => false,
            };
        }
        mod_set
    }
    /// Returns the modifies statments from the specificaiton map for the given function
    fn mod_set_from_spec_map(&self, func_name: &str) -> Option<HashSet<String>> {
        self.specs_map
            .get(func_name)
            .and_then(|spec_vec| {
                Some(
                    spec_vec
                        .iter()
                        .cloned()
                        .filter(|spec| spec.is_modifies())
                        .map(|spec| {
                            spec.mod_set()
                                .iter()
                                .map(|v| v.name.clone())
                                .collect::<Vec<String>>()
                        })
                        .flatten()
                        .collect::<HashSet<String>>(),
                )
            })
            .map_or(None, |s| Some(s))
    }
    /// Returns the requires statments from the specification map for the given function
    fn requires_from_spec_map(
        &self,
        func_name: &str,
        arg_decls: &Vec<Expr>,
    ) -> Result<Vec<Spec>, utils::Error> {
        let mut requires = self
            .specs_map
            .get(func_name)
            .and_then(|spec_vec| {
                Some(
                    spec_vec
                        .iter()
                        .cloned()
                        .filter(|spec| spec.is_requires())
                        .map(|spec| spec)
                        .collect::<Vec<Spec>>(),
                )
            })
            .map_or(vec![], |v| v);
        // Add pc entry requirement
        requires.push(Spec::Requires(Expr::op_app(
            Op::Comp(CompOp::Equality),
            vec![
                Expr::Var(self.pc_var()),
                Expr::bv_lit(*self.get_func_entry_addr(func_name)?, self.xlen),
            ],
        )));
        // Add argument constraints
        for (i, arg) in arg_decls.iter().enumerate() {
            let var = arg.get_expect_var();
            let extend_width = self.xlen - var.typ.get_expect_bv_width();
            requires.push(Spec::Requires(Expr::op_app(
                Op::Comp(CompOp::Equality),
                vec![
                    Expr::var(&format!("$a{}", i), Type::Bv { w: self.xlen }),
                    Expr::op_app(
                        Op::Bv(BVOp::ZeroExt),
                        vec![
                            arg.clone(),
                            Expr::bv_lit(extend_width, var.typ.get_expect_bv_width()),
                        ],
                    ),
                ],
            )));
        }
        Ok(requires)
    }
    /// Returns ensures stating that pc is eventually the return address
    fn pc_eventually_ra_spec(&self) -> Spec {
        // Add pc eventually returns constraint
        Spec::Ensures(Expr::op_app(
            Op::Comp(CompOp::Equality),
            vec![
                Expr::Var(self.pc_var()),
                Expr::op_app(
                    Op::Bv(BVOp::Concat),
                    vec![
                        Expr::op_app(
                            Op::Bv(BVOp::Slice { l: 63, r: 1 }),
                            vec![Expr::op_app(
                                Op::Old,
                                vec![Expr::var("$ra", self.bv_type(self.xlen))],
                            )],
                        ),
                        Expr::bv_lit(0, 1),
                    ],
                ),
            ],
        ))
    }
    /// Returns ensure statments from specification map for the given function
    fn ensures_from_spec_map(&self, func_name: &str) -> Option<Vec<Spec>> {
        let ensures = self
            .specs_map
            .get(func_name)
            .and_then(|spec_vec| {
                Some(
                    spec_vec
                        .iter()
                        .cloned()
                        .filter(|spec| spec.is_ensures())
                        .map(|spec| spec)
                        .collect::<Vec<Spec>>(),
                )
            })
            .map_or(None, |v| Some(v));
        ensures
    }
    /// Translates DwarfTypeDefn to Type
    fn dwarf_typ_to_ir(&self, typ: &DwarfTypeDefn) -> Type {
        match &typ {
            DwarfTypeDefn::Primitive { bytes } => Type::Bv {
                w: bytes * utils::BYTE_SIZE,
            },
            DwarfTypeDefn::Array { .. }
            | DwarfTypeDefn::Struct { .. }
            | DwarfTypeDefn::Pointer { .. } => Type::Bv { w: self.xlen },
        }
    }
    /// List of callee addresses in the CFG
    fn get_callee_addrs(&self, cfg: &Rc<Cfg>) -> HashSet<u64> {
        cfg.bbs()
            .iter()
            .map(|(_entry_addr, bb)| {
                bb.insts()
                    .iter()
                    .filter(|al| al.base_instruction_name() == "jal")
                    .map(|al| al.imm().unwrap().get_imm_val() as u64)
                    .collect::<Vec<u64>>()
            })
            .flatten()
            .filter(|addr| self.is_func_entry(&addr.to_string()[..]))
            .collect::<HashSet<u64>>()
    }
    /// Basic block procedure name
    fn bb_proc_name(&self, addr: u64) -> String {
        format!("bb_{:#x}", addr)
    }
    /// Instruction interface procedure name
    fn inst_proc_name(&self, op_code: &str) -> String {
        format!("{}_proc", op_code)
    }
    /// The set of system state variables
    fn pc_var(&self) -> Var {
        Var {
            name: PC_VAR.to_string(),
            typ: self.bv_type(self.xlen),
        }
    }
    /// Memory state variable
    fn mem_var(&self) -> Var {
        Var {
            name: MEM_VAR.to_string(),
            typ: self.mem_type(),
        }
    }
    /// Privilege state variable
    fn priv_var(&self) -> Var {
        Var {
            name: PRIV_VAR.to_string(),
            typ: self.bv_type(2),
        }
    }
    /// Expection state variable
    fn except_var(&self) -> Var {
        Var {
            name: EXCEPT_VAR.to_string(),
            typ: self.bv_type(self.xlen),
        }
    }
    /// A vector of the state variables
    fn sys_state_vars(&self) -> Vec<Var> {
        let mut vec_var = vec![];
        vec_var.push(self.pc_var());
        vec_var.push(self.mem_var());
        vec_var.push(self.priv_var());
        vec_var.push(self.except_var());
        vec_var
    }
    /// Returns the type of memory (XLEN addressable byte valued array)
    fn mem_type(&self) -> Type {
        Type::Array {
            in_typs: vec![Box::new(self.bv_type(self.xlen))],
            out_typ: Box::new(self.bv_type(utils::BYTE_SIZE)),
        }
    }
    /// Returns a bitvector type of specified width
    fn bv_type(&self, width: u64) -> Type {
        Type::Bv { w: width }
    }
    /// Infers registers used by the instructions in the CFG
    fn infer_vars(&self, cfg_rc: &Rc<Cfg>) -> Vec<Var> {
        let mut var_names = vec![];
        for (_entry_addr, bb) in cfg_rc.bbs() {
            for al in bb.insts() {
                let mut regs: [Option<&InstOperand>; 4] = [al.rd(), al.rs1(), al.rs2(), al.csr()];
                for reg_op in regs.iter_mut() {
                    if let Some(reg) = reg_op {
                        var_names.push(reg.to_string());
                    }
                }
            }
        }
        var_names.dedup();
        var_names
            .iter()
            .cloned()
            .map(|vid| Var {
                name: vid,
                typ: self.bv_type(self.xlen),
            })
            .collect::<Vec<Var>>()
    }
    /// Returns the CFG of the function named `func_name`
    fn get_func_cfg(&self, func_name: &str) -> Result<&Rc<Cfg>, utils::Error> {
        self.func_cfg_map.get(func_name).map_or(
            Err(utils::Error::TranslatorErr(format!(
                "Could not find function {} cfg.",
                func_name
            ))),
            |rc| Ok(rc),
        )
    }
    /// Retuns true if and only if the addr is a function entry address
    fn is_func_entry(&self, addr: &str) -> bool {
        self.func_cfg_map.get(addr).is_some()
    }
    /// Returns the function name with entry address `addr`
    fn get_func_name(&self, addr: &u64) -> Option<String> {
        self.func_cfg_map
            .get(&addr.to_string()[..])
            .map_or(None, |cfg| {
                Some(
                    cfg.bbs().get(addr).unwrap().insts()[0]
                        .function_name()
                        .to_string(),
                )
            })
    }
    /// Returns the entry address of the function named `func_name`
    fn get_func_entry_addr(&self, func_name: &str) -> Result<&u64, utils::Error> {
        Ok(self.get_func_cfg(func_name)?.get_entry_addr())
    }
    /// Returns the CFG for the function containg the address `addr`
    fn get_func_cfg_addr(&self, addr: &u64) -> Result<&Rc<Cfg>, utils::Error> {
        self.func_cfg_map
            .iter()
            .find(|(_, cfg)| {
                cfg.bbs()
                    .keys()
                    .find(|bb_entry| bb_entry == &addr)
                    .is_some()
            })
            .map_or(
                Err(utils::Error::TranslatorErr(format!(
                    "Could not find function cfg containing a basic block with entry address {}.",
                    addr
                ))),
                |rc| Ok(rc.1),
            )
    }
    /// Returns the function defined at address "addr"
    fn func_at_addr(&self, addr: &u64) -> Option<String> {
        if let Some(cfg) = self.get_func_cfg_addr(addr).ok() {
            cfg.get_basic_blk(*addr).map_or(None, |bb| {
                Some(
                    bb.insts()
                        .iter()
                        .next()
                        .unwrap()
                        .function_name()
                        .to_string(),
                )
            })
        } else {
            None
        }
    }
}
