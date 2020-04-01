use std::collections::{HashMap, HashSet};
use std::rc::Rc;

use crate::readers::disassembler::Inst;

#[derive(Debug)]
pub struct Cfg<T>
where
    T: Inst + std::fmt::Debug + std::fmt::Display,
{
    /// Entry address of the CFG
    entry_addr: u64,
    /// CFG nodes
    nodes: HashMap<u64, Rc<CfgNode<T>>>,
}

#[derive(Debug)]
pub struct CfgNode<T>
where
    T: Inst + std::fmt::Debug + std::fmt::Display,
{
    /// The basic blocks for the CFG node
    bb: Rc<BasicBlock<T>>,
    /// Successors by entry addresses of basic blocks
    succs: Vec<u64>,
}

pub struct CfgNodeIterator<'a, T>
where
    T: Inst + std::fmt::Debug + std::fmt::Display,
{
    node: &'a CfgNode<T>,
    index: usize,
}

#[derive(Debug)]
pub struct BasicBlock<T>
where
    T: Inst + std::fmt::Debug + std::fmt::Display,
{
    /// Instructions of the basic block
    insts: Vec<Rc<T>>,
}

impl<T> Cfg<T>
where
    T: Inst + std::fmt::Debug + std::fmt::Display,
{
    /// Creates a new Cfg object starting at the entry address
    pub fn new(entry_addr: u64, bbs: &HashMap<u64, Rc<BasicBlock<T>>>) -> Cfg<T> {
        // Initialize cfg
        let mut cfg = Cfg {
            entry_addr,
            nodes: HashMap::new(),
        };
        // Populate the CFG starting from the entry address
        cfg.create_cfg(entry_addr, &bbs);
        cfg.print();
        cfg
    }
    /// Recursively builds a CFG starting with the entry address
    fn create_cfg(&mut self, entry_addr: u64, bbs: &HashMap<u64, Rc<BasicBlock<T>>>) {
        if self.nodes.get(&entry_addr).is_some() {
            return;
        }
        let bb = bbs.get(&entry_addr).expect(&format!(
            "Unable to find basic block at {:#x?}.",
            entry_addr
        ));
        let succs = bb.exit().successors();
        // Update the current node in the CFG nodes map
        let cfg_node = Rc::new(CfgNode::new(Rc::clone(&bb), succs.clone()));
        self.nodes.insert(entry_addr, cfg_node);
        // Recursively compute the successor nodes
        for succ in &succs {
            self.create_cfg(*succ, bbs);
        }
    }
    /// Returns the entry address
    pub fn entry_addr(&self) -> &u64 {
        &self.entry_addr
    }
    /// Returns the CfgNode at the entry address
    pub fn entry_node(&self) -> Rc<CfgNode<T>> {
        let entry = self
            .nodes
            .get(&self.entry_addr)
            .expect(&format!("Invalid CFG entry address {}.", self.entry_addr));
        Rc::clone(entry)
    }
    /// Returns a map of address to CFG nodes
    pub fn nodes(&self) -> &HashMap<u64, Rc<CfgNode<T>>> {
        &self.nodes
    }
    /// Returns a cycle in the CFG
    pub fn find_cycle(&self, ignore: &dyn Fn(u64) -> bool, current_node: &u64, seen_nodes: &mut HashSet<u64>, processed_cycle: &mut bool) -> Option<Vec<u64>> {
        if seen_nodes.contains(current_node) {
            return Some(vec![*current_node]);
        }
        seen_nodes.insert(*current_node);
        let cfg_node = self.nodes
        	.get(current_node)
        	.expect(&format!("Unable to find CFG node at address {}.", current_node));
        for addr in cfg_node.exit().successors() {
        	if  ignore(addr) {
        		continue;
        	}
            if let Some(mut cycle) = self.find_cycle(ignore, &addr, seen_nodes, processed_cycle) {
                if !*processed_cycle {
                    cycle.push(*current_node);
                }
                if cycle[0] == *current_node {
                    *processed_cycle = true;
                }
                return Some(cycle);
            }
        }
        seen_nodes.remove(current_node);
        None
    }
    /// Prints the CFG in a more readable format
    pub fn print(&self) {
    	info!("========== Created CFG ===========");
        for (addr, cfg_node) in self.nodes() {
            info!("====== CfgNode entry address: {:#x?} ======", addr);
            for al in cfg_node.into_iter() {
                info!("{}", al.to_string());
            }
        }
    }
}

impl<T> CfgNode<T>
where
    T: Inst + std::fmt::Debug + std::fmt::Display,
{
    /// Creates a new CfgNode with the given basic block and successors
    pub fn new(bb: Rc<BasicBlock<T>>, succs: Vec<u64>) -> CfgNode<T> {
        CfgNode { bb, succs }
    }
    /// Returns the entry node
    pub fn entry(&self) -> Rc<T> {
        Rc::clone(&self.bb.entry())
    }
    /// Returns the exit node
    pub fn exit(&self) -> Rc<T> {
        Rc::clone(&self.bb.exit())
    }
    /// Returns the list of instructions
    fn insts(&self) -> &Vec<Rc<T>> {
        &self.bb.insts
    }
}

impl<'a, T> IntoIterator for &'a CfgNode<T>
where
    T: Inst + std::fmt::Debug + std::fmt::Display,
{
    type Item = Rc<T>;
    type IntoIter = CfgNodeIterator<'a, T>;
    fn into_iter(self) -> Self::IntoIter {
        CfgNodeIterator {
            node: self,
            index: 0,
        }
    }
}

impl<'a, T> Iterator for CfgNodeIterator<'a, T>
where
    T: Inst + std::fmt::Debug + std::fmt::Display,
{
    type Item = Rc<T>;
    fn next(&mut self) -> Option<Rc<T>> {
        if self.index < self.node.insts().len() {
            let res = Rc::clone(&self.node.insts()[self.index]);
            self.index += 1;
            Some(res)
        } else {
            None
        }
    }
}

impl<T> BasicBlock<T>
where
    T: Inst + std::fmt::Debug + std::fmt::Display,
{
    /// Creates a new basic block
    pub fn new(insts: Vec<Rc<T>>) -> BasicBlock<T> {
        BasicBlock { insts }
    }
    /// Splits a set of instruction lines into basic blocks
    pub fn split(lines: &Vec<Rc<T>>) -> HashMap<u64, Rc<BasicBlock<T>>> {
        let mut entry_pts = HashSet::new();
        let mut exit_pts = HashSet::new();
        let mut iter = lines.iter();
        // Iterate through the remaining lines
        let mut prev_was_jump = true;
        while let Some(line) = iter.next() {
            if prev_was_jump {
                entry_pts.insert(line.address());
            }
            if line.is_jump() {
                // Jumps are exits
                let exit = line.address();
                exit_pts.insert(exit);
                // Their successors are entries
                for succ in line.successors() {
                    entry_pts.insert(succ);
                }
                prev_was_jump = true;
            } else {
                prev_was_jump = false;
            }
        }
        // Partition the instructions into basic blocks
        let mut bb_map = HashMap::new();
        let mut insts = vec![];
        let mut curr_entry = None;
        for line in lines {
            let addr = line.address();
            // Begin new basic block starting at this starting point
            if entry_pts.contains(&addr) {
                if let Some(ce_addr) = curr_entry {
                    if addr != ce_addr && insts.len() > 0 {
                        // End basic block
                        let bb = Rc::new(BasicBlock::new(insts.clone()));
                        bb_map.insert(curr_entry.unwrap(), bb);
                        insts = vec![];
                    }
                }
                curr_entry = Some(addr);
            }
            // Add instruction into the current basic block
            insts.push(Rc::clone(line));
            // Add basic block ending at this exit point
            if exit_pts.contains(&addr) {
                let bb = Rc::new(BasicBlock::new(insts.clone()));
                bb_map.insert(curr_entry.unwrap(), bb);
                insts = vec![];
            }
        }
        bb_map
    }
    /// Returns the exit instruction
    pub fn exit(&self) -> Rc<T> {
        let last = self
            .insts
            .last()
            .expect("Basic block contains no elements.");
        Rc::clone(&last)
    }
    /// Returns the instruction at entry
    pub fn entry(&self) -> Rc<T> {
        let first = self
            .insts
            .first()
            .expect("Basic block contains no elements.");
        Rc::clone(&first)
    }
}
