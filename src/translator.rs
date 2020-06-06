use std::boxed::Box;
use std::collections::HashMap;
use std::collections::HashSet;
use std::marker::PhantomData;
use std::rc::Rc;
use topological_sort::TopologicalSort;

use crate::ast::*;
use crate::datastructures::cfg;
use crate::ir_interface::IRInterface;
use crate::readers::disassembler;
use crate::readers::disassembler::Inst;
use crate::readers::dwarfreader::DwarfCtx;
use crate::spec_lang::sl_ast;
use crate::system_model;
use crate::utils;

/// Instruction level translator from RISC-V to verification IR
pub struct Translator<'t, I>
where
    I: IRInterface,
{
    /// ====== Translator Inputs ========
    /// Width of integer register in bits (FIXME: also currently used for address length)
    xlen: u64,
    /// Verification model
    model: Model,
    /// List of assembly instructions
    bbs: &'t HashMap<u64, Rc<cfg::BasicBlock<disassembler::AssemblyLine>>>,
    /// A set of the functions to ignore
    ignored_funcs: &'t HashSet<&'t str>,
    /// A list of functions to verify
    verify_funcs: &'t Vec<&'t str>,
    /// DWARF debugging information
    dwarf_ctx: &'t DwarfCtx,
    /// Map of specs from function name to a list of pre/post conditions
    specs_map: &'t HashMap<String, Vec<sl_ast::Spec>>,
    /// Flag indicating if the translator will ignore specs
    /// When true, all function pre and post conditions are ignored
    /// and functions are all inlined
    ignore_specs: bool,
    /// ========== Context ================
    /// Map of function names / labels to entry addresses
    labels_to_addr: HashMap<String, u64>,
    /// Memoize map for generated functions at the given address
    cfg_memo: HashMap<u64, Rc<cfg::Cfg<disassembler::AssemblyLine>>>,
    /// Generated functions / labels
    generated: HashSet<u64>,
    /// Map of procedure name to thier modifies set
    mod_set_map: HashMap<String, HashSet<String>>,
    /// ========= Phantom Data ==========
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
        bbs: &'t HashMap<u64, Rc<cfg::BasicBlock<disassembler::AssemblyLine>>>,
        ignored_funcs: &'t HashSet<&'t str>,
        verify_funcs: &'t Vec<&'t str>,
        dwarf_ctx: &'t DwarfCtx,
        specs_map: &'t HashMap<String, Vec<sl_ast::Spec>>,
        ignore_specs: bool,
    ) -> Self {
        Translator {
            xlen: xlen,
            model: Model::new(module_name),
            bbs: bbs,
            ignored_funcs: ignored_funcs,
            verify_funcs: verify_funcs,
            dwarf_ctx: dwarf_ctx,
            specs_map: specs_map,
            ignore_specs: ignore_specs,
            labels_to_addr: Translator::<I>::create_label_to_addr_map(bbs),
            cfg_memo: HashMap::new(),
            generated: HashSet::new(),
            mod_set_map: HashMap::new(),
            _phantom_i: PhantomData,
        }
    }
    // =============================================================================
    // ==================== Translator context =====================================
    // =============================================================================

    /// Clear translator context
    pub fn clear(&mut self) {
        self.model = Model::new(&self.model.name);
        self.generated = HashSet::new();
    }
    /// Returns a map of labels / function names to entry addresses
    fn create_label_to_addr_map(
        bbs: &HashMap<u64, Rc<cfg::BasicBlock<disassembler::AssemblyLine>>>,
    ) -> HashMap<String, u64> {
        let mut label_to_addr = HashMap::new();
        for (_, bb) in bbs {
            if bb.entry().is_label_entry() {
                let name = bb.entry().function_name().to_string();
                let addr = bb.entry().address();
                label_to_addr.insert(name, addr);
            }
        }
        label_to_addr
    }

    // =============================================================================
    // ==================== Printing functions =====================================
    // =============================================================================
    /// Outputs the model into output stream
    pub fn print_model(&self) -> String {
        I::model_to_string(
            &self.xlen,
            &self.model,
            &self.dwarf_ctx,
            &self.ignored_funcs,
            &self.verify_funcs,
        )
    }
    // =============================================================================
    // ==================== Main translation functions =============================
    // =============================================================================

    /// Generates a stub function model
    pub fn gen_func_model_stub(&mut self, func_name: &str) {
        let arg_exprs = self
            .func_args(func_name)
            .iter()
            .map(|expr| {
                let var = expr.get_expect_var();
                Expr::var(&var.name, system_model::bv_type(self.xlen))
            })
            .collect();
        let mod_set = self.mod_set_from_spec_map(func_name);
        let requires = if !self.ignore_specs {
            self.requires_from_spec_map(func_name)
        } else {
            None
        };
        let ensures = if !self.ignore_specs {
            self.ensures_from_spec_map(func_name)
        } else {
            None
        };
        let tracked = self.tracked_from_spec_map(func_name);
        let ret = None;
        let entry_addr = *self
            .func_entry_addr(func_name)
            .expect(&format!("Unable to find {}'s entry address.", func_name));
        let stub_fm = FuncModel::new(
            func_name,
            entry_addr,
            arg_exprs,
            ret,
            requires,
            ensures,
            tracked,
            mod_set,
            Stmt::Block(vec![]),
            false,
        );
        self.model.add_func_model(stub_fm);
    }
    /// Generates a model for the function at address "addr"
    pub fn gen_func_model(&mut self, func_name: &str) {
        // Don't generate already generated functions
        let func_entry = *self
            .func_entry_addr(func_name)
            .expect(&format!("Unable to find {}'s entry address.", func_name));
        if self.generated.get(&func_entry).is_some() {
            return;
        }
        self.generated.insert(func_entry);
        // Generate stub function models for ignored functions
        if self.ignored_funcs.get(func_name).is_some() {
            self.gen_func_model_stub(func_name);
            return;
        }
        // Get the function cfg
        let func_cfg = self.get_func_cfg(func_entry);

        // ======= State variables ======= //
        // FIXME: Remove these later; these variables should be predefined for RISC-V architectures.
        // Add global variables for the function block
        self.model.add_vars(&self.infer_vars(&func_cfg));
        // Add system variables
        self.model
            .add_vars(&system_model::sys_state_vars(self.xlen));

        // ====== Basic Block Function Models ==== //
        // Generate procedure model for each basic block
        let bb_fms = func_cfg
            .nodes()
            .iter()
            .map(|(addr, bb)| {
                let bb_proc_name = self.bb_proc_name(*addr);
                let body = self.cfg_node_to_block(bb);
                let mod_set = self.infer_mod_set(&body);
                FuncModel::new(
                    &bb_proc_name,
                    *addr,
                    vec![],
                    None,
                    None,
                    None,
                    None,
                    Some(mod_set),
                    body,
                    true,
                )
            })
            .collect::<Vec<_>>();
        // ====== Modifies sets ======= //
        // Add all basic block mod sets to the model
        let bb_mod_sets = bb_fms
            .iter()
            .map(|fm| (fm.sig.name.clone(), fm.sig.mod_set.clone()))
            .collect::<Vec<(String, HashSet<String>)>>();
        for bb_mod_set in bb_mod_sets {
            self.mod_set_map.insert(bb_mod_set.0, bb_mod_set.1);
        }
        // Modifies set for the current function
        let mut mod_set = bb_fms
            .iter()
            .map(|bb_fm| bb_fm.sig.mod_set.clone())
            .flatten()
            .collect::<HashSet<String>>();
        // Add basic block function models to the model
        self.model.add_func_models(bb_fms);
        // ======== Recursively Generate Callees ======== //
        let callees = self.get_callee_addrs(func_name, &func_cfg);
        for (target, _) in &callees {
            if let Ok(name) = self.get_func_at(target) {
                self.gen_func_model(&name[..]);
            }
        }
        // Add callee modifies set to this function's modifies set
        for (target, _) in &callees {
            if let Ok(name) = self.get_func_at(target) {
                if !self.ignored_funcs.contains(&name[..]) {
                    continue;
                }
                if self.ignored_funcs.get(&name[..]).is_some() {
                    if let Some(ms) = self.mod_set_from_spec_map(func_name) {
                        mod_set = mod_set.union(&ms).cloned().collect();
                    } else {
                        // FIXME: Warn that we haven't provided a modifies set here?
                    }
                } else {
                    let callee_ms = self
                        .mod_set_map
                        .get(&name)
                        .expect(&format!("Unable to find modifies set for {}.", name));
                    mod_set = mod_set.union(callee_ms).cloned().collect();
                }
            }
        }
        // Memo current mod set
        self.mod_set_map
            .insert(func_name.to_string(), mod_set.clone());
        // Get arguments of function
        let arg_exprs = self
            .func_args(func_name)
            .iter()
            .map(|expr| {
                let var = expr.get_expect_var();
                Expr::var(&var.name, system_model::bv_type(self.xlen))
            })
            .collect();
        // Translate specs
        // let requires = if !self.ignore_specs {
        //     self.requires_from_spec_map(func_name, &arg_exprs).ok()
        // } else {
        //     None
        // };
        // let ensures = if !self.ignore_specs {
        //     self.ensures_from_spec_map(func_name)
        // } else {
        //     None
        // };
        // let tracked = self.tracked_from_spec_map(func_name);
        let requires = if !self.ignore_specs {
            self.requires_from_spec_map(func_name)
        } else {
            None
        };
        let ensures = if !self.ignore_specs {
            self.ensures_from_spec_map(func_name)
        } else {
            None
        };
        let tracked = self.tracked_from_spec_map(func_name);
        // Create the procedure body
        let body = self.cfg_to_symbolic_blk(&func_entry, &func_cfg);
        // let ret = self.func_ret_type(func_name);
        let ret = None;
        // Add the function to the verification model
        self.model.add_func_model(FuncModel::new(
            func_name,
            func_entry,
            arg_exprs,
            ret,
            requires,
            ensures,
            tracked,
            Some(mod_set),
            body,
            self.ignore_specs,
        ));
    }

    /// Returns the inferred modifies set
    fn infer_mod_set(&self, stmt: &Stmt) -> HashSet<String> {
        let mut mod_set = HashSet::new();
        mod_set.insert(system_model::PC_VAR.to_string());
        mod_set.insert(system_model::RETURNED_FLAG.to_string());
        mod_set.insert(system_model::MEM_VAR.to_string());
        match stmt {
            Stmt::FuncCall(fc) => {
                // Add modifies set if it's a function call
                if let Some(fc_mod_set) = self.mod_set_map.get(&fc.func_name) {
                    mod_set = mod_set.union(&fc_mod_set).cloned().collect();
                }
                // Add the left hand assignments
                let lhs = fc
                    .lhs
                    .iter()
                    .map(|v| v.get_expect_var().name.to_string())
                    .collect::<HashSet<_>>();
                mod_set = mod_set.union(&lhs).cloned().collect();
            }
            Stmt::Assign(a) => {
                let lhs_mod_set = a
                    .lhs
                    .iter()
                    .map(|e| match e {
                        // Either the LHS is a register, returned, pc, etc
                        Expr::Var(v, _) => v.name.clone(),
                        // Or memory (for stores)
                        _ => system_model::MEM_VAR.to_string(),
                    })
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
    /// Returns a block statement for the CFG
    fn cfg_to_symbolic_blk(
        &self,
        func_entry_addr: &u64,
        cfg_rc: &Rc<cfg::Cfg<disassembler::AssemblyLine>>,
    ) -> Stmt {
        let mut stmts_vec = vec![];
        let sorted_entries = self.topo_sort(cfg_rc);
        for bb_entry in sorted_entries {
            let cfg_node = cfg_rc.nodes().get(&bb_entry).expect(&format!(
                "Unable to find CFG node with entry address {}.",
                bb_entry
            ));
            // Skip basic blocks that are entry addresses to functions (except for this function)
            // FIXME: This is not tested well. Check if trap_vector is properly generated.
            // Sometimes there are functions (e.g. trap_vector) that call basic blocks
            // from other functions. If this happens, we want to create a model that
            // contains basic blocks from both functions.
            if cfg_node.entry().is_label_entry() && bb_entry != *func_entry_addr {
                continue;
            }
            // Basic block call
            let bb_call_stmt =
                Box::new(Stmt::func_call(self.bb_proc_name(bb_entry), vec![], vec![]));
            let then_blk_stmt = Stmt::Block(vec![bb_call_stmt]);
            let guarded_call = Box::new(self.guarded_call(&bb_entry, then_blk_stmt));
            stmts_vec.push(guarded_call);
            // Function call
            // If the instruction is a jump and the target is
            // another function's entry address, then make a call to it.
            if cfg_node.exit().op() == disassembler::JAL {
                let target_addr = cfg_node
                    .exit()
                    .imm()
                    .expect("Invalid format: JAL is missing a target address.")
                    .get_imm_val() as u64;
                let target_cfg_node = cfg_rc.nodes().get(&target_addr).expect(&format!(
                    "Unable to find CFG node with entry address {}.",
                    bb_entry
                ));
                if target_cfg_node.entry().is_label_entry() {
                    let f_name = self
                        .get_func_at(&target_addr)
                        .expect(&format!("Could not find function entry at {}.", bb_entry));
                    let f_args = self
                        .func_args(&f_name)
                        .iter()
                        .enumerate()
                        .map(|(i, arg_expr)| {
                            let arg_var = arg_expr.get_expect_var();
                            Expr::var(&format!("a{}", i), arg_var.typ.clone())
                        })
                        .collect::<Vec<_>>();
                    let lhss = vec![];
                    // if let Some(_) = self.func_ret_type(&f_name) {
                    //     lhss.push(Expr::var(
                    //         system_model::A0,
                    //         system_model::bv_type(self.xlen),
                    //     ));
                    // }
                    let f_call_stmt = Box::new(Stmt::func_call(f_name, lhss, f_args));
                    let mut then_stmts = vec![];
                    // Add function call to then statement
                    then_stmts.push(f_call_stmt);
                    // Reset the returned variable for the caller
                    then_stmts.push(Box::new(Stmt::assign(
                        vec![Expr::var(
                            system_model::RETURNED_FLAG,
                            system_model::bv_type(1),
                        )],
                        vec![Expr::bv_lit(0, 1)],
                    )));
                    let then_blk_stmt = Stmt::Block(then_stmts);
                    let guarded_call = Box::new(self.guarded_call(&target_addr, then_blk_stmt));
                    stmts_vec.push(guarded_call)
                }
            }
        }
        stmts_vec.push(Box::new(Stmt::assign(
            vec![Expr::var(
                system_model::RETURNED_FLAG,
                system_model::bv_type(1),
            )],
            vec![Expr::bv_lit(1, 1)],
        )));
        Stmt::Block(stmts_vec)
    }
    /// Returns a guarded block statement
    /// Guards are pc == target and returned == false
    fn guarded_call(&self, entry: &u64, blk: Stmt) -> Stmt {
        let if_pc_guard = Expr::op_app(
            Op::Comp(CompOp::Equality),
            vec![
                Expr::Var(
                    system_model::pc_var(self.xlen),
                    system_model::bv_type(self.xlen),
                ),
                Expr::bv_lit(*entry, self.xlen),
            ],
        );
        let if_returned_guard = Expr::op_app(
            Op::Comp(CompOp::Equality),
            vec![
                Expr::var(system_model::RETURNED_FLAG, system_model::bv_type(1)),
                Expr::bv_lit(0, 1),
            ],
        );
        let if_guard = Expr::op_app(Op::Bool(BoolOp::Conj), vec![if_pc_guard, if_returned_guard]);
        let then_blk_stmt = Box::new(blk);
        // Return the guarded call
        Stmt::if_then_else(if_guard, then_blk_stmt, None)
    }
    /// Returns a topological sort of the cfg as an array of entry addresses
    fn topo_sort(&self, cfg_rc: &Rc<cfg::Cfg<disassembler::AssemblyLine>>) -> Vec<u64> {
        let mut ts = TopologicalSort::<u64>::new();
        // Initialize the first entry address of the CFG
        ts.insert(*cfg_rc.entry_addr());
        // Closure that determines the subgraphs to ignore by entry address
        let ignore = |addr| {
            self.get_func_at(&addr).is_ok()
                && self
                    .ignored_funcs
                    .contains(&self.get_func_at(&addr).unwrap()[..])
        };
        // Recursively update ts to contain all the dependencies between basic blocks in the CFG
        self.compute_deps(
            &ignore,
            cfg_rc,
            cfg_rc.entry_addr(),
            &mut ts,
            &mut HashSet::new(),
        );
        // Convert to an array of sorted addresses by dependency
        let mut sorted = vec![];
        loop {
            let mut v = ts.pop_all();
            if v.is_empty() {
                if ts.len() != 0 {
                    // If ts.pop_all() is empty and len() != 0, there is a cycle
                    let cycle = cfg_rc
                        .find_cycle(
                            &ignore,
                            cfg_rc.entry_addr(),
                            &mut HashSet::new(),
                            &mut false,
                        )
                        .expect("Should have found a cycle.");
                    panic!(
                        "There is a cycle in the cfg of {:?}: {:?}.",
                        self.get_func_at(&cfg_rc.entry_addr()),
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
    /// Recursively computes the dependency graph given the entry address
    /// However, it ignores all subgraphs rooted at cfg nodes with an entry address
    /// in which the closure "ignore" returns true for.
    fn compute_deps(
        &self,
        ignore: &dyn Fn(u64) -> bool,
        cfg_rc: &Rc<cfg::Cfg<disassembler::AssemblyLine>>,
        curr: &u64,
        ts: &mut TopologicalSort<u64>,
        processed: &mut HashSet<u64>,
    ) {
        if processed.contains(curr) {
            return;
        }
        processed.insert(*curr);
        if let Some(cfg_node) = cfg_rc.nodes().get(curr) {
            let entry = cfg_node.entry().address();
            if ignore(entry) {
                return;
            }
            for target in cfg_node.exit().successors() {
                ts.add_dependency(entry, target);
                // If the entry address is to a function entry,
                // then there is no need to recursively compute
                // the dependents of the callee because
                if cfg_rc
                    .nodes()
                    .get(&target)
                    .expect("Unable to find target basic block.")
                    .entry()
                    .is_label_entry()
                {
                    continue;
                }
                // Otherwise, recursively compute the dependencies of the target
                self.compute_deps(ignore, cfg_rc, &target, ts, processed);
            }
        } else {
            panic!("Unable to find basic block at {}", curr);
        }
    }
    /// Returns the function defined at the address "addr"
    fn get_func_at(&self, addr: &u64) -> Result<String, utils::Error> {
        let entry_blk = self
            .bbs
            .get(addr)
            .expect(&format!("Could not find basic block at {}.", addr))
            .entry();
        if entry_blk.is_label_entry() {
            Ok(entry_blk.function_name().to_string())
        } else {
            Err(utils::Error::TranslatorErr(format!(
                "{} is not a function entry address.",
                entry_blk.address()
            )))
        }
    }
    /// Returns a list of callee addresses and the lines they were called at
    ///
    /// # EXAMPLE
    /// 0000000080004444 <osm_pmp_set+0xc> jal  zero,0000000080004d58 <pmp_set>
    /// The line above would be added as (0000000080004d58, 0000000080004444)
    fn get_callee_addrs(
        &self,
        func_name: &str,
        cfg_rc: &Rc<cfg::Cfg<disassembler::AssemblyLine>>,
    ) -> Vec<(u64, u64)> {
        let mut callee_addrs = vec![];
        for (_, cfg_node) in cfg_rc.nodes() {
            for al in cfg_node.into_iter() {
                if al.function_name() != func_name {
                    continue;
                }
                if al.op() == disassembler::JAL {
                    callee_addrs.push((al.imm().unwrap().get_imm_val() as u64, al.address()));
                }
            }
        }
        callee_addrs
    }
    /// Returns the function name for basic blocks
    fn bb_proc_name(&self, addr: u64) -> String {
        format!("bb_{:#x?}", addr)
    }
    /// Returns a block statement given representing the basic block
    fn cfg_node_to_block(&self, bb: &Rc<cfg::CfgNode<disassembler::AssemblyLine>>) -> Stmt {
        let mut stmt_vec = vec![];
        for al in bb.into_iter() {
            // stmt_vec.push(Box::new(self.al_to_ir(&al)));
            stmt_vec.push(Box::new(self.al_to_ir_stmt(&al)));
        }
        Stmt::Block(stmt_vec)
    }
    /// Returns the statment containing the instruction specs
    fn al_to_ir_stmt(&self, al: &Rc<disassembler::AssemblyLine>) -> Stmt {
        // Destination registers
        let mut dsts = vec![];
        let mut regs: [Option<&disassembler::InstOperand>; 2] = [al.rd(), al.csr()];
        for reg_op in regs.iter_mut() {
            if let Some(reg) = reg_op {
                dsts.push(Expr::var(
                    &reg.get_reg_name()[..],
                    system_model::bv_type(self.xlen),
                ));
                assert!(!reg.has_offset());
            }
        }
        // Source registers
        let mut srcs = vec![];
        let mut regs: [Option<&disassembler::InstOperand>; 3] = [al.rs1(), al.rs2(), al.csr()];
        for reg_op in regs.iter_mut() {
            if let Some(reg) = reg_op {
                let reg_name = &reg.get_reg_name()[..];
                match reg_name {
                    // Replace the zero register with a 0 constant
                    // the zero register is used as a placeholder for
                    // writing to in the verification models
                    "zero" => srcs.push(Expr::bv_lit(0, self.xlen)),
                    _ => srcs.push(Expr::var(reg_name, system_model::bv_type(self.xlen))),
                }
                if reg.has_offset() {
                    srcs.push(Expr::bv_lit(reg.get_reg_offset() as u64, self.xlen));
                }
            }
        }
        if let Some(operand) = al.imm() {
            srcs.push(Expr::bv_lit(operand.get_imm_val() as u64, self.xlen));
        }
        match al.op() {
            "add" => {
                system_model::add_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "sub" => {
                system_model::sub_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "mul" => {
                system_model::mul_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "sll" => {
                system_model::sll_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "slt" => {
                system_model::slt_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "sltu" => system_model::sltu_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "xor" => {
                system_model::xor_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "srl" => {
                system_model::srl_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "sra" => {
                system_model::sra_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "or" => {
                system_model::or_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "and" => {
                system_model::and_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "addw" => system_model::addw_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "subw" => system_model::subw_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "sllw" => system_model::sllw_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "srlw" => system_model::srlw_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "sraw" => system_model::sraw_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "jalr" => system_model::jalr_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "lb" => {
                system_model::lb_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "lh" => {
                system_model::lh_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "lw" => {
                system_model::lw_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "lbu" => {
                system_model::lbu_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "lhu" => {
                system_model::lhu_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "addi" => system_model::addi_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "slti" => system_model::slti_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "sltiu" => system_model::sltiu_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "xori" => system_model::xori_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "ori" => {
                system_model::ori_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "andi" => system_model::andi_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "slli" => system_model::slli_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "srli" => system_model::srli_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "srai" => system_model::srai_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "lwu" => {
                system_model::lwu_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "ld" => {
                system_model::ld_inst(dsts[0].clone(), srcs[0].clone(), srcs[1].clone(), self.xlen)
            }
            "addiw" => system_model::addiw_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "slliw" => system_model::slliw_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "srliw" => system_model::srliw_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "sraiw" => system_model::sraiw_inst(
                dsts[0].clone(),
                srcs[0].clone(),
                srcs[1].clone(),
                self.xlen,
            ),
            "sb" => {
                system_model::sb_inst(srcs[0].clone(), srcs[1].clone(), srcs[2].clone(), self.xlen)
            }
            "sh" => {
                system_model::sh_inst(srcs[0].clone(), srcs[1].clone(), srcs[2].clone(), self.xlen)
            }
            "sw" => {
                system_model::sw_inst(srcs[0].clone(), srcs[1].clone(), srcs[2].clone(), self.xlen)
            }
            "sd" => {
                system_model::sd_inst(srcs[0].clone(), srcs[1].clone(), srcs[2].clone(), self.xlen)
            }
            "beq" => {
                system_model::beq_inst(srcs[0].clone(), srcs[1].clone(), srcs[2].clone(), self.xlen)
            }
            "bne" => {
                system_model::bne_inst(srcs[0].clone(), srcs[1].clone(), srcs[2].clone(), self.xlen)
            }
            "blt" => {
                system_model::blt_inst(srcs[0].clone(), srcs[1].clone(), srcs[2].clone(), self.xlen)
            }
            "bge" => {
                system_model::bge_inst(srcs[0].clone(), srcs[1].clone(), srcs[2].clone(), self.xlen)
            }
            "bltu" => system_model::bltu_inst(
                srcs[0].clone(),
                srcs[1].clone(),
                srcs[2].clone(),
                self.xlen,
            ),
            "bgeu" => system_model::bgeu_inst(
                srcs[0].clone(),
                srcs[1].clone(),
                srcs[2].clone(),
                self.xlen,
            ),
            "lui" => system_model::lui_inst(dsts[0].clone(), srcs[0].clone(), self.xlen),
            "auipc" => system_model::auipc_inst(dsts[0].clone(), srcs[0].clone(), self.xlen),
            "jal" => system_model::jal_inst(dsts[0].clone(), srcs[0].clone(), self.xlen),
            _ => system_model::unimplemented_inst(al.op(), self.xlen),
        }
    }
    /// Constructs and returns a pointer to a Cfg with entry address addr
    fn get_func_cfg(&mut self, addr: u64) -> Rc<cfg::Cfg<disassembler::AssemblyLine>> {
        if let Some(cfg_rc) = self.cfg_memo.get(&addr) {
            return Rc::clone(cfg_rc);
        }
        let entry_bb = self
            .bbs
            .get(&addr)
            .expect(&format!("Unable to basic block at {}.", addr));
        assert!(
            &entry_bb.entry().is_label_entry(),
            format!("{} is not an entry address to a function.", addr)
        );
        let cfg = Rc::new(cfg::Cfg::new(addr, &self.bbs));
        self.cfg_memo.insert(addr, Rc::clone(&cfg));
        cfg
    }
    /// Infer register variables from cfg.
    /// FIXME: Remove this function, eventually the system model should be entirely predefined.
    fn infer_vars(&self, cfg_rc: &Rc<cfg::Cfg<disassembler::AssemblyLine>>) -> HashSet<Var> {
        let mut var_names = vec![];
        for (_, cfg_node) in cfg_rc.nodes() {
            for al in cfg_node.into_iter() {
                let mut regs: [Option<&disassembler::InstOperand>; 4] =
                    [al.rd(), al.rs1(), al.rs2(), al.csr()];
                for reg_op in regs.iter_mut() {
                    if let Some(reg) = reg_op {
                        var_names.push(reg.to_string());
                    }
                }
            }
        }
        var_names
            .iter()
            .cloned()
            .map(|vid| Var {
                name: vid,
                typ: system_model::bv_type(self.xlen),
            })
            .collect::<HashSet<Var>>()
    }
    /// Returns the arguments of a function from the DWARF context
    fn func_args(&self, func_name: &str) -> Vec<Expr> {
        self.dwarf_ctx
            .func_sig(func_name)
            .ok()
            .and_then(|fs| {
                Some(
                    fs.args
                        .iter()
                        // .map(|x| Expr::var(&x.name[..], self.dwarf_typ_to_ir(&x.typ_defn)))
                        .map(|x| Expr::var(&x.name[..], x.typ_defn.to_ir_type()))
                        .collect::<Vec<Expr>>(),
                )
            })
            .map_or(vec![], |v| v)
    }

    #[allow(dead_code)]
    /// DEAD_CODE: Function is currently not used because we don't
    ///            use the return type in the function sig (for now).
    /// Returns the return type of a function from the DWARF context
    fn func_ret_type(&self, func_name: &str) -> Option<Type> {
        self.dwarf_ctx.func_sig(func_name).ok().and_then(|fs| {
            // fs.ret_type.as_ref().and_then(|rd| Some(self.dwarf_typ_to_ir(rd.as_ref())))
            fs.ret_type
                .as_ref()
                .and_then(|_| Some(Type::Bv { w: self.xlen }))
        })
    }

    /// Returns the entry address of the function named `func_name`
    fn func_entry_addr(&self, func_name: &str) -> Option<&u64> {
        self.labels_to_addr.get(func_name)
    }

    // =============================================================================
    // ==================== Specification translation ==============================
    // =============================================================================

    /// Returns a vector of specifications from function named `func_name` if
    /// it exists in the specification map `spec_map`
    /// It filters out the specifications according to sfilter
    fn filter_from_spec_map(
        &self,
        func_name: &str,
        sfilter: fn(&sl_ast::Spec) -> bool,
    ) -> Option<Vec<sl_ast::Spec>> {
        let specs = match self.specs_map.get(func_name) {
            Some(spec_vec) => spec_vec
                .iter()
                .filter(|spec| sfilter(*spec))
                .cloned()
                .collect::<Vec<sl_ast::Spec>>(),
            None => return None,
        };
        Some(specs)
    }

    /// Returns a single hash set containing all variables in the modifies set(s)
    fn mod_set_from_spec_map(&mut self, func_name: &str) -> Option<HashSet<String>> {
        let sfilter = |s: &sl_ast::Spec| match s {
            sl_ast::Spec::Modifies(..) => true,
            _ => false,
        };
        let specs = self.filter_from_spec_map(func_name, sfilter);
        // Combine the modifies set if there are any (we only need one)
        match specs {
            Some(specs) => {
                let combined_modset = specs
                    .iter()
                    .map(|spec| match &*spec {
                        sl_ast::Spec::Modifies(hs) => hs,
                        _ => panic!("Should have filtered non modifies specifications."),
                    })
                    .flatten()
                    .cloned()
                    .collect::<HashSet<String>>();
                Some(combined_modset)
            }
            None => None,
        }
    }

    /// Returns a vector of require statements for function `func_name`
    fn requires_from_spec_map(&self, func_name: &str) -> Option<Vec<sl_ast::Spec>> {
        let sfilter = |s: &sl_ast::Spec| match s {
            sl_ast::Spec::Requires(..) => true,
            _ => false,
        };
        self.filter_from_spec_map(func_name, sfilter)
    }

    /// Returns a vector of ensure statements for function `func_name`
    fn ensures_from_spec_map(&self, func_name: &str) -> Option<Vec<sl_ast::Spec>> {
        let sfilter = |s: &sl_ast::Spec| match s {
            sl_ast::Spec::Ensures(..) => true,
            _ => false,
        };
        self.filter_from_spec_map(func_name, sfilter)
    }

    /// Returns a vector of track statements for function `func_name`
    fn tracked_from_spec_map(&self, func_name: &str) -> Option<Vec<sl_ast::Spec>> {
        let sfilter = |s: &sl_ast::Spec| match s {
            sl_ast::Spec::Track(..) => true,
            _ => false,
        };
        self.filter_from_spec_map(func_name, sfilter)
    }
}
