use std::boxed::Box;
use std::collections::HashMap;
use std::collections::HashSet;
use std::marker::PhantomData;
use std::rc::Rc;

use topological_sort::TopologicalSort;

use crate::dwarfreader::{DwarfInterface, DwarfReader, DwarfTypeDefn};
use crate::ir::*;
use crate::objectdumpreader::*;
use crate::utils::*;

/// Constants
pub const PC_VAR: &str = "pc";
pub const MEM_VAR: &str = "mem";
pub const PRIV_VAR: &str = "current_priv";
pub const EXCEPT_VAR: &str = "exception";

/// Translator
pub struct Translator<'t, I, J>
where
    I: IRInterface<DwarfReader = DwarfReader<J>>,
    J: DwarfInterface,
{
    xlen: u64,
    model: Model,
    func_cfg_map: &'t HashMap<String, Rc<Cfg>>,
    generated_funcs: HashSet<String>,
    ignored_funcs: &'t HashSet<&'t str>,
    mod_set_map: HashMap<String, HashSet<String>>,
    dwarf_reader: Rc<DwarfReader<J>>,
    specs_map: &'t Option<HashMap<String, Vec<Spec>>>,
    _phantom_i: PhantomData<I>,
}

impl<'t, I, J> Translator<'t, I, J>
where
    I: IRInterface<DwarfReader = DwarfReader<J>>,
    J: DwarfInterface,
{
    pub fn new(
        func_cfg_map: &'t HashMap<String, Rc<Cfg>>,
        ignored_funcs: &'t HashSet<&'t str>,
        dwarf_reader: Rc<DwarfReader<J>>,
        specs_map: &'t Option<HashMap<String, Vec<Spec>>>,
    ) -> Self {
        Translator {
            xlen: 64, // TODO: Support for other architecture widths
            model: Model::new(),
            func_cfg_map,
            generated_funcs: HashSet::new(),
            ignored_funcs,
            mod_set_map: HashMap::new(),
            dwarf_reader,
            specs_map,
            _phantom_i: PhantomData,
        }
    }
    pub fn print_model(&self) {
        println!(
            "{}",
            I::model_to_string(&self.xlen, &self.model, Rc::clone(&self.dwarf_reader))
        );
    }
    pub fn gen_func_model_stub(&mut self, name: &str) {
        let stub_fm = FuncModel {
            sig: FuncSig::new(name, vec![], None, vec![], vec![], HashSet::new()),
            body: Stmt::Block(vec![]),
            inline: false,
        };
        self.model.add_func_model(stub_fm);
    }
    pub fn gen_func_model(&mut self, func_name: &str) -> Result<(), Error> {
        if self.ignored_funcs.get(func_name).is_some() {
            self.gen_func_model_stub(func_name);
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
        // Fixme: Compute modifies set to block (NOTE: What does this even mean?)
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
        // Find translate the specification
        let mut requires = self
            .specs_map
            .as_ref()
            .and_then(|specs_map| Some(specs_map.get(func_name)))
            .and_then(|spec_vec| {
                spec_vec.and_then(|v| {
                    Some(
                        v.iter()
                            .cloned()
                            .filter(|spec| spec.is_requires())
                            .map(|spec| spec)
                            .collect::<Vec<Spec>>(),
                    )
                })
            })
            .map_or(vec![], |v| v);
        let ensures = self
            .specs_map
            .as_ref()
            .and_then(|specs_map| Some(specs_map.get(func_name)))
            .and_then(|spec_vec| {
                spec_vec.and_then(|v| {
                    Some(
                        v.iter()
                            .cloned()
                            .filter(|spec| spec.is_ensures())
                            .map(|spec| spec)
                            .collect::<Vec<Spec>>(),
                    )
                })
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
        // Get the arguments
        let arg_decls = self.func_args(func_name);
        let ret_decl = None;
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
    /// Computes the arguments of a function from the DWARF info
    fn func_args(&self, func_name: &str) -> Vec<Expr> {
        self.dwarf_reader
            .func_sig(func_name)
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
    fn gen_func_body(&self, cfg: &Rc<Cfg>) -> Stmt {
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
    fn basic_blk_call(&self, entry_addr: u64, cfg: &Rc<Cfg>) -> Stmt {
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
        // Add call statement to callee function
        if let Some(target_addr) = cfg.next_abs_jump_addr(entry_addr) {
            if self.is_func_entry(&target_addr.to_string()[..]) {
                let func_name = self.get_func_name(target_addr).unwrap();
                let args = self
                    .dwarf_reader
                    .func_sig(&func_name)
                    .and_then(|fs| {
                        Some(
                            fs.args
                                .iter()
                                .enumerate()
                                .map(|(i, dwarf_var)| {
                                    let reg_var = Expr::var(&format!("a{}", i), Type::Unknown);
                                    let typ = self.dwarf_typ_to_ir(&dwarf_var.typ_defn);
                                    Expr::op_app(
                                        Op::Bv(BVOp::Slice {
                                            l: typ.get_expect_bv_width(),
                                            r: 0,
                                        }),
                                        vec![reg_var],
                                    )
                                })
                                .collect::<Vec<_>>(),
                        )
                    })
                    .map_or(vec![], |v| v);
                let call_stmt = Stmt::func_call(func_name, vec![], args);
                then_stmts_inner.push(Box::new(call_stmt));
                then_stmts_inner.push(Box::new(Stmt::Assert(fallthru_guard.unwrap().clone())));
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
        for (entry_addr, _bb) in cfg.bbs() {
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
    /// Translates DwarfTypeDefn to Type
    fn dwarf_typ_to_ir(&self, typ: &DwarfTypeDefn) -> Type {
        match &typ {
            DwarfTypeDefn::Primitive { bytes } => Type::Bv {
                w: bytes * BYTE_SIZE,
            },
            DwarfTypeDefn::Array { .. }
            | DwarfTypeDefn::Struct { .. }
            | DwarfTypeDefn::Pointer { .. } => Type::Bv { w: self.xlen },
        }
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
    fn mem_var(&self) -> Var {
        Var {
            name: MEM_VAR.to_string(),
            typ: self.mem_type(),
        }
    }
    fn priv_var(&self) -> Var {
        Var {
            name: PRIV_VAR.to_string(),
            typ: self.bv_type(2),
        }
    }
    fn except_var(&self) -> Var {
        Var {
            name: EXCEPT_VAR.to_string(),
            typ: self.bv_type(self.xlen),
        }
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
    fn mem_type(&self) -> Type {
        Type::Array {
            in_typs: vec![Box::new(self.bv_type(self.xlen))],
            out_typ: Box::new(self.bv_type(BYTE_SIZE)),
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
    fn get_func_cfg(&self, func_name: &str) -> Result<&Rc<Cfg>, Error> {
        self.func_cfg_map.get(func_name).map_or(
            Err(Error::TErr {
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
    fn get_func_entry_addr(&self, func_name: &str) -> Result<&u64, Error> {
        Ok(self.get_func_cfg(func_name)?.get_entry_addr())
    }
    #[allow(dead_code)]
    fn get_func_cfg_addr(&self, addr: &str) -> Result<&Rc<Cfg>, Error> {
        self.func_cfg_map.get(addr).map_or(
            Err(Error::TErr {
                msg: format!("Could not find function at addr {}.", addr),
            }),
            |rc| Ok(rc),
        )
    }
}
