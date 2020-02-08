use std::boxed::Box;
use std::collections::HashMap;
use std::collections::HashSet;
use std::fmt;
use std::marker::PhantomData;
use std::rc::Rc;

use crate::ir::*;
use crate::objectdumpreader::*;
use crate::utils::*;

/// Translator
pub struct Translator<'t, I>
where
    I: IRInterface,
{
    xlen: u64,
    model: Model,
    func_cfg_map: &'t HashMap<String, Rc<Cfg>>,
    generated_funcs: HashSet<String>,
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
            _phantom_i: PhantomData,
        }
    }
    pub fn gen_func_model_stub(&mut self, name: &str) {
        let stub_fm = FuncModel {
            sig: FuncSig::new(name, vec![], None, vec![], vec![]),
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
        let fms = self
            .get_func_cfg(func_name)?
            .bbs()
            .iter()
            .map(|(entry_addr, bb)| {
                let bb_proc_name = self.bb_proc_name(*entry_addr);
                let body = self.bb_to_block(bb);
                FuncModel::new(&bb_proc_name, vec![], None, vec![], vec![], body, true)
            })
            .collect::<Vec<_>>();
        self.model.add_func_models(fms);
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
        let body = Stmt::Block(vec![]);
        // Add function model
        self.model.add_func_model(FuncModel::new(func_name, arg_decls, ret_decl, requires, ensures, body, false));
        Ok(())
    }
    pub fn print_model(&self) {
        println!("{}", I::ir_model_to_string(&self.model));
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
                lhs.push(Rc::new(Expr::Var(Var::new(
                    &reg.get_reg_name()[..],
                    self.bv_type(reg.get_reg_size() as u64),
                ))));
            }
        }
        // inputs
        let mut operands = vec![];
        let mut regs: [Option<&InstOperand>; 3] = [al.rs1(), al.rs2(), al.csr()];
        for reg_op in regs.iter_mut() {
            if let Some(reg) = reg_op {
                operands.push(Rc::new(Expr::Var(Var::new(
                    &reg.get_reg_name()[..],
                    self.bv_type(reg.get_reg_size() as u64),
                ))));
            }
        }
        // immediate input
        if let Some(imm) = al.imm() {
            operands.push(Rc::new(Expr::Literal(Literal::bv(
                imm.get_imm_val() as u64,
                20,
            ))));
        }
        Stmt::FuncCall(FuncCall {
            func_name,
            lhs,
            operands,
        })
    }
    /// =================== Helper functions ===================
    fn get_callee_addrs(&self, cfg: &Rc<Cfg>) -> Vec<u64> {
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
            .collect::<Vec<u64>>()
    }
    fn bb_proc_name(&self, addr: u64) -> String {
        format!("bb_{:#x}", addr)
    }
    fn inst_proc_name(&self, op_code: &str) -> String {
        format!("{}_proc", op_code)
    }
    fn sys_state_vars(&self) -> Vec<Var> {
        let mut vec_var = vec![];
        vec_var.push(Var::new("pc", self.bv_type(self.xlen)));
        vec_var.push(Var::new("mem", self.mem_type()));
        vec_var.push(Var::new("current_priv", self.bv_type(2)));
        vec_var.push(Var::new("exception", self.bv_type(self.xlen)));
        vec_var
    }
    fn mem_type(&self) -> Rc<Type> {
        Rc::new(Type::Array {
            in_typs: vec![self.bv_type(self.xlen)],
            out_typ: self.bv_type(8),
        })
    }
    fn bv_type(&self, width: u64) -> Rc<Type> {
        Rc::new(Type::Bv { w: width })
    }
    // FIXME: return set (what did i mean here?)
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
