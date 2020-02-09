use std::boxed::Box;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::marker::PhantomData;
use std::rc::Rc;

use topological_sort::TopologicalSort;

use crate::ir::*;
use crate::objectdumpreader::*;
use crate::utils::*;

/// Constants
const PC_VAR: &str = "pc";
const MEM_VAR: &str = "mem";
const PRIV_VAR: &str = "current_priv";
const EXCEPT_VAR: &str = "exception";

/// Translator
pub struct Translator<'t, I>
where
    I: IRInterface,
{
    xlen: u64,
    model: Model,
    func_cfg_map: &'t HashMap<String, Rc<Cfg>>,
    generated_funcs: HashSet<String>,
    modifies_set: HashMap<String, HashSet<String>>,
    _phantom_i: PhantomData<I>,
}

impl<'t, I> Translator<'t, I>
where
    I: IRInterface,
{
    pub fn new(func_cfg_map: &'t HashMap<String, Rc<Cfg>>) -> Self {
        Translator {
            xlen: 64,
            model: Model::new(),
            func_cfg_map: func_cfg_map,
            generated_funcs: HashSet::new(),
            modifies_set: HashMap::new(),
            _phantom_i: PhantomData,
        }
    }
    pub fn gen_func_model_stub(&mut self, name: &str) {
        let stub_fm = FuncModel {
            sig: FuncSig::new(name, vec![], None, vec![], vec![], HashSet::new()),
            body: Stmt::Block(vec![]),
            inline: false,
        };
        self.model.add_func_model(stub_fm);
    }
    pub fn gen_func_model(&mut self, func_name: &str) -> Result<(), TErr> {
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
        // Fixme: Compute modifies set to block
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
                    vec![],
                    None,
                    vec![],
                    vec![],
                    mod_set,
                    body,
                    true,
                )
            })
            .collect::<Vec<_>>();
        let func_mod_set = bb_fms
            .iter()
            .map(|bb_fm| bb_fm.sig.mod_set.clone())
            .flatten()
            .collect::<HashSet<String>>();
        self.model.add_func_models(bb_fms);
        // Depth first recursive call (required
        // to happen before we create the current function
        // because we need to compute the modifies set)
        let callees = self.get_callee_addrs(self.get_func_cfg(func_name)?);
        for callee in callees {
            assert!(
                self.is_func_entry(&callee.to_string()[..]),
                format!("Address {} was not found or not an entry point.", callee)
            );
            let callee_name = self.get_func_name(&callee).unwrap();
            self.gen_func_model(&callee_name[..]);
        }
        // Find translate the specification
        let mut requires = vec![];
        let mut ensures = vec![];
        // Get the arguments
        let arg_decls = vec![];
        let ret_decl = None;
        // Create the cfg
        let body = self.gen_func_body(self.get_func_cfg(func_name)?);
        // Add function model
        self.model.add_func_model(FuncModel::new(
            func_name,
            arg_decls,
            ret_decl,
            requires,
            ensures,
            func_mod_set,
            body,
            false,
        ));
        Ok(())
    }
    pub fn print_model(&self) {
        println!("{}", I::ir_model_to_string(&self.model));
    }
    /// Function model body
    fn gen_func_body(&self, cfg: &Rc<Cfg>) -> Stmt {
        let mut stmts_vec = vec![];
        let top_sort = self.topological_sort(&cfg);
        // Add basic blocks in topological order
        let callees = self.get_callee_addrs(&cfg);
        for entry_addr in top_sort {
            // Ignore callee function calls
            if callees.get(&entry_addr).is_some() {
                continue;
            } else {
                stmts_vec.push(Rc::new(self.basic_blk_call(entry_addr, cfg)));
            }
        }
        Stmt::Block(stmts_vec)
    }
    /// Basic block call in function body
    fn basic_blk_call(&self, entry_addr: u64, cfg: &Rc<Cfg>) -> Stmt {
        let mut then_stmts_inner = vec![];
        // Add call to basic block
        let call_stmt =
            Stmt::FuncCall(FuncCall::new(self.bb_proc_name(entry_addr), vec![], vec![]));
        then_stmts_inner.push(Rc::new(call_stmt));
        // Assert statements for jump targets
        let mut fallthru_guard = None;
        let mut jump_guard = None;
        let mut callee_call = false;
        // Fall through target
        if let Some(target_addr) = cfg.next_blk_addr(entry_addr) {
            fallthru_guard = Some(Expr::OpApp(OpApp::new(
                Op::Comp(CompOp::Equality),
                vec![
                    Expr::Var(self.pc_var()),
                    Expr::Literal(Literal::bv(*target_addr, self.xlen)),
                ],
            )));
        }
        // Jump target (remove fall through if target is function entry; ie. JAL)
        if let Some(target_addr) = cfg.next_abs_jump_addr(entry_addr) {
            if self.is_func_entry(&target_addr.to_string()[..]) {
                callee_call = true;
            }
            jump_guard = Some(Expr::OpApp(OpApp::new(
                Op::Comp(CompOp::Equality),
                vec![
                    Expr::Var(self.pc_var()),
                    Expr::Literal(Literal::bv(*target_addr, self.xlen)),
                ],
            )));
        }
        // Add guard for after basic block
        if fallthru_guard.is_some() && jump_guard.is_some() && !callee_call {
            then_stmts_inner.push(Rc::new(Stmt::Assert(Expr::OpApp(OpApp::new(
                Op::Bool(BoolOp::Disj),
                vec![fallthru_guard.clone().unwrap(), jump_guard.clone().unwrap()],
            )))));
        } else if jump_guard.is_some() {
            then_stmts_inner.push(Rc::new(Stmt::Assert(jump_guard.clone().unwrap())));
        } else if fallthru_guard.is_some() {
            then_stmts_inner.push(Rc::new(Stmt::Assert(fallthru_guard.clone().unwrap())));
        }
        // Add call statement to callee function
        if let Some(target_addr) = cfg.next_abs_jump_addr(entry_addr) {
            if self.is_func_entry(&target_addr.to_string()[..]) {
                let call_stmt = Stmt::FuncCall(FuncCall::new(
                    self.get_func_name(target_addr).unwrap(),
                    vec![],
                    vec![],
                ));
                then_stmts_inner.push(Rc::new(call_stmt));
                then_stmts_inner.push(Rc::new(Stmt::Assert(fallthru_guard.unwrap().clone())));
            }
        }
        let then_stmt = Box::new(Stmt::Block(then_stmts_inner));
        // Add condition that checks if pc == basic block entry address
        let cond = Expr::OpApp(OpApp::new(
            Op::Comp(CompOp::Equality),
            vec![
                Expr::Var(self.pc_var()),
                Expr::Literal(Literal::bv(entry_addr, self.xlen)),
            ],
        ));
        Stmt::IfThenElse(IfThenElse::new(cond, then_stmt, None))
    }
    /// Topologically sorted list of entry addresses in the CFG
    fn topological_sort(&self, cfg: &Rc<Cfg>) -> Vec<u64> {
        let mut sorted = vec![];
        let mut ts = TopologicalSort::<&u64>::new();
        for (entry_addr, bb) in cfg.bbs() {
            if let Some(target) = cfg.next_blk_addr(*entry_addr) {
                ts.add_dependency(entry_addr, target);
            }
            if let Some(target) = cfg.next_abs_jump_addr(*entry_addr) {
                ts.add_dependency(entry_addr, target);
            }
        }
        loop {
            let mut v = ts.pop_all();
            if v.is_empty() {
                if ts.len() != 0 {
                    // If ts.pop_all() is empty and len() != 0, there is a cycle
                    panic!("There is a cyclic cfg in {:#?}", cfg);
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
    fn bb_to_block(&self, bb: &BasicBlock) -> Stmt {
        let mut inst_vec = vec![];
        for al in bb.insts() {
            inst_vec.push(Rc::new(self.al_to_ir(&al)));
        }
        Stmt::Block(inst_vec)
    }
    fn al_to_ir(&self, al: &Rc<AssemblyLine>) -> Stmt {
        let func_name = self.inst_proc_name(al.base_instruction_name());
        // outputs
        let mut lhs = vec![];
        let mut regs: [Option<&InstOperand>; 2] = [al.rd(), al.csr()];
        for reg_op in regs.iter_mut() {
            if let Some(reg) = reg_op {
                lhs.push(Expr::Var(Var::new(
                    &reg.get_reg_name()[..],
                    self.bv_type(reg.get_reg_size() as u64),
                )));
            }
        }
        // inputs
        let mut operands = vec![];
        let mut regs: [Option<&InstOperand>; 3] = [al.rs1(), al.rs2(), al.csr()];
        for reg_op in regs.iter_mut() {
            if let Some(reg) = reg_op {
                operands.push(Expr::Var(Var::new(
                    &reg.get_reg_name()[..],
                    self.bv_type(reg.get_reg_size() as u64),
                )));
            }
        }
        // immediate input
        if let Some(imm) = al.imm() {
            operands.push(Expr::Literal(Literal::bv(imm.get_imm_val() as u64, 20)));
        }
        Stmt::FuncCall(FuncCall::new(func_name, lhs, operands))
    }
    /// =================== Helper functions ===================
    /// Compute modifies set for a basic block
    fn bb_mod_set(&self, bb: &BasicBlock) -> HashSet<String> {
        let mut mod_set = HashSet::new();
        mod_set.insert(PC_VAR.to_string());
        for al in bb.insts() {
            if let Some(reg) = al.rd() {
                mod_set.insert(reg.get_reg_name());
            }
            match al.base_instruction_name() {
                "sb" | "sh" | "sw" | "sd" => mod_set.insert(MEM_VAR.to_string()),
                _ => false,
            };
        }
        mod_set
    }
    /// List of callee addresses in the CFG
    fn get_callee_addrs(&self, cfg: &Rc<Cfg>) -> HashSet<u64> {
        cfg.bbs()
            .iter()
            .map(|(entry_addr, bb)| {
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
        Var::new(PC_VAR, self.bv_type(self.xlen))
    }
    fn mem_var(&self) -> Var {
        Var::new(MEM_VAR, self.mem_type())
    }
    fn priv_var(&self) -> Var {
        Var::new(PRIV_VAR, self.bv_type(2))
    }
    fn except_var(&self) -> Var {
        Var::new(EXCEPT_VAR, self.bv_type(self.xlen))
    }
    fn sys_state_vars(&self) -> Vec<Var> {
        let mut vec_var = vec![];
        vec_var.push(self.pc_var());
        vec_var.push(self.mem_var());
        vec_var.push(self.priv_var());
        vec_var.push(self.except_var());
        vec_var
    }
    /// Returns the type of memory (XLEN addressable byte valued array)
    fn mem_type(&self) -> Rc<Type> {
        Rc::new(Type::Array {
            in_typs: vec![self.bv_type(self.xlen)],
            out_typ: self.bv_type(8),
        })
    }
    /// Returns a bitvector type of specified width
    fn bv_type(&self, width: u64) -> Rc<Type> {
        Rc::new(Type::Bv { w: width })
    }
    /// Infers registers used by the instructions in the CFG
    fn infer_vars(&self, cfg_rc: &Rc<Cfg>) -> Vec<Var> {
        let mut var_names = vec![];
        for (entry_addr, bb) in cfg_rc.bbs() {
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
    fn get_func_cfg(&self, func_name: &str) -> Result<&Rc<Cfg>, TErr> {
        self.func_cfg_map.get(func_name).map_or(
            Err(TErr {
                msg: format!("Could not find function {}.", func_name),
            }),
            |rc| Ok(rc),
        )
    }
    fn is_func_entry(&self, addr: &str) -> bool {
        self.func_cfg_map.get(addr).is_some()
    }
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
    fn get_func_cfg_addr(&self, addr: &str) -> Result<&Rc<Cfg>, TErr> {
        self.func_cfg_map.get(addr).map_or(
            Err(TErr {
                msg: format!("Could not find function at addr {}.", addr),
            }),
            |rc| Ok(rc),
        )
    }
}
