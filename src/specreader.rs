use std::collections::{HashMap, HashSet};
use std::fs;

use pest::iterators::Pair;
use pest::Parser;

use crate::dwarfreader::DwarfCtx;
use crate::ir;
use crate::utils;

#[derive(Parser)]
#[grammar = "pest/speclang.pest"]
pub struct SpecReader<'s> {
    xlen: u64,
    dwarf_ctx: &'s DwarfCtx,
}

impl<'s> SpecReader<'s> {
    pub fn new(xlen: u64, dwarf_ctx: &'s DwarfCtx) -> SpecReader {
        SpecReader { xlen, dwarf_ctx }
    }

    pub fn process_specs_file(
        &self,
        spec_file_path: &str,
    ) -> Result<HashMap<String, Vec<ir::Spec>>, utils::Error> {
        let specs_str = fs::read_to_string(spec_file_path)
            .expect("[get_specs] Failed to open specification file.");
        self.parse_specs(&specs_str[..])
    }

    pub fn parse_specs(
        &self,
        specs_string: &str,
    ) -> Result<HashMap<String, Vec<ir::Spec>>, utils::Error> {
        match SpecReader::parse(Rule::func_specs, specs_string) {
            Ok(mut func_specs_pair) => {
                let mut func_specs_inner = func_specs_pair
                    .next()
                    .expect("[parse_specs] Could not find function specifications.")
                    .into_inner();
                let mut function_specs_map = HashMap::new();
                while let Some(spec) = func_specs_inner.next() {
                    let mut spec_inner = spec.into_inner();
                    let spec_pair = match spec_inner.next() {
                        Some(pair) => pair,
                        None => break,
                    };
                    let func_name = SpecReader::get_func_name(spec_pair)?;
                    let mut function_specs_vec = vec![];
                    while let Some(spec_stmt_pair) = spec_inner.next() {
                        let spec_stmt = self.translate_spec_stmt(&func_name, spec_stmt_pair)?;
                        function_specs_vec.push(spec_stmt);
                    }
                    function_specs_map.insert(func_name, function_specs_vec);
                }
                Ok(function_specs_map)
            }
            Err(e) => Err(utils::Error::SpecParseError(format!(
                "Unable to parse spec {:?}.",
                e
            ))),
        }
    }

    fn get_func_name(pair: Pair<Rule>) -> Result<String, utils::Error> {
        match pair.as_rule() {
            Rule::func_name => {
                let mut inner = pair.into_inner();
                let func_name = inner
                    .next()
                    .expect("[get_func_name] The first child should be the function name.")
                    .as_str();
                Ok(String::from(func_name))
            }
            _ => Err(utils::Error::SpecParseError(
                "Could not get function name in spec.".to_string(),
            )),
        }
    }

    fn translate_spec_stmt(
        &self,
        func_name: &str,
        pair: Pair<Rule>,
    ) -> Result<ir::Spec, utils::Error> {
        match pair.as_rule() {
            Rule::spec_stmt => {
                let mut spec_stmt_inner = pair.into_inner();
                let spec_type = spec_stmt_inner.next().unwrap().as_str();
                let expr = self.translate_expr(func_name, spec_stmt_inner.next().unwrap())?;
                match spec_type {
                    "requires" => Ok(ir::Spec::Requires(expr)),
                    "ensures" => Ok(ir::Spec::Ensures(expr)),
                    _ => Err(utils::Error::SpecParseError(
                        "Invalid spec line.".to_string(),
                    )),
                }
            }
            Rule::mod_stmt => Ok(ir::Spec::Modifies(self.translate_mod_set(pair)?)),
            _ => Err(utils::Error::SpecParseError(
                "Unable to translate spec statement.".to_string(),
            )),
        }
    }

    fn translate_mod_set(&self, pair: Pair<Rule>) -> Result<HashSet<ir::Var>, utils::Error> {
        let mut mod_set = HashSet::new();
        let mut inner = pair.into_inner();
        while let Some(e) = inner.next() {
            let var_str = e.as_str();
            mod_set.insert(ir::Var {
                name: var_str.to_string(),
                typ: ir::Type::Unknown,
            });
        }
        Ok(mod_set)
    }

    fn translate_expr(&self, func_name: &str, pair: Pair<Rule>) -> Result<ir::Expr, utils::Error> {
        let rule = pair.as_rule();
        let pair_str = pair.as_str();
        let mut inner = pair.into_inner();
        match rule {
            Rule::old => {
                let inner_expr = self.translate_expr(func_name, inner.next().unwrap())?;
                Ok(ir::Expr::op_app(ir::Op::Old, vec![inner_expr]))
            }
            Rule::value_expr | Rule::bool_expr | Rule::get_field | Rule::array_index => {
                self.translate_expr(func_name, inner.next().unwrap())
            }
            Rule::comp_eval | Rule::bool_eval | Rule::bv_eval => {
                let v1 = self.translate_expr(func_name, inner.next().unwrap())?;
                let op = self.translate_op(inner.next().unwrap())?;
                let v2 = self.translate_expr(func_name, inner.next().unwrap())?;
                Ok(ir::Expr::op_app(op, vec![v1, v2]))
            }
            Rule::unary_bool_eval => {
                let op = self.translate_op(inner.next().unwrap())?;
                let v = self.translate_expr(func_name, inner.next().unwrap())?;
                Ok(ir::Expr::op_app(op, vec![v]))
            }
            Rule::bool_const => Ok(ir::Expr::bool_lit(pair_str == "true")),
            Rule::integer => Ok(ir::Expr::bv_lit(
                utils::dec_str_to_i64(pair_str).unwrap() as u64,
                self.xlen,
            )),
            Rule::bitvec => {
                let mut iter = pair_str.split("bv");
                let val = iter.next().unwrap();
                let width = iter.next().unwrap();
                Ok(ir::Expr::bv_lit(
                    utils::dec_str_to_u64(val).unwrap(),
                    utils::dec_str_to_u64(width).unwrap(),
                ))
            }
            Rule::path | Rule::path_ref => {
                let path_ref = rule == Rule::path_ref;
                let mut path = self.translate_expr(func_name, inner.next().unwrap())?;
                // Check if it's a function reference (which is assumed to be a variable during the first translation pass)
                if path_ref && path.is_var() && self.dwarf_ctx.is_func(&path.get_expect_var().name) {
                    // return Ok(ir::Expr::bv_lit(self.dwarf_ctx.func_sig(&path.get_expect_var().name)?.entry_addr, self.xlen));
                    let id = &path.get_expect_var().name;
                    let func_app_name = utils::global_func_addr_name(id);
                    return Ok(ir::Expr::func_app(func_app_name, vec![]));
                }
                let is_global_var = self
                    .dwarf_ctx
                    .global_var(&path.get_expect_var().name)
                    .is_ok();
                let is_ptr_type = self
                    .dwarf_ctx
                    .func_sig(func_name)?
                    .args
                    .iter()
                    .find(|v| v.typ_defn.is_ptr_type())
                    .is_some();
                while let Some(e) = inner.next() {
                    match e.as_rule() {
                        Rule::array_index => {
                            path = ir::Expr::op_app(
                                ir::Op::ArrayIndex,
                                vec![path, self.translate_expr(func_name, e)?],
                            );
                        }
                        Rule::get_field => {
                            path = ir::Expr::op_app(
                                ir::Op::GetField(
                                    e.into_inner().next().unwrap().as_str().to_string(),
                                ),
                                vec![path],
                            );
                        }
                        _ => panic!("[translate_expr] Not a valid path."),
                    }
                }
                // TODO: Are globals usually always pointers?
                if !path_ref && (is_global_var || is_ptr_type) {
                    path = ir::Expr::op_app(ir::Op::Deref, vec![path]);
                }
                Ok(path)
            }
            Rule::identifier => Ok(ir::Expr::var(pair_str, ir::Type::Unknown)),
            _ => panic!("Unsupported rule. {:#?} {:#?}", rule, inner),
        }
    }

    fn translate_op(&self, pair: Pair<Rule>) -> Result<ir::Op, utils::Error> {
        let rule = pair.as_rule();
        let pair_str = pair.as_str();
        match rule {
            Rule::comp_op => match pair_str {
                "==" => Ok(ir::Op::Comp(ir::CompOp::Equality)),
                "!=" => Ok(ir::Op::Comp(ir::CompOp::Inequality)),
                "<" => Ok(ir::Op::Comp(ir::CompOp::Lt)),
                "<=" => Ok(ir::Op::Comp(ir::CompOp::Le)),
                ">" => Ok(ir::Op::Comp(ir::CompOp::Gt)),
                ">=" => Ok(ir::Op::Comp(ir::CompOp::Ge)),
                "<_u" => Ok(ir::Op::Comp(ir::CompOp::Ltu)),
                "<=_u" => Ok(ir::Op::Comp(ir::CompOp::Leu)),
                ">_u" => Ok(ir::Op::Comp(ir::CompOp::Gtu)),
                ">=_u" => Ok(ir::Op::Comp(ir::CompOp::Geu)),
                _ => Err(utils::Error::SpecParseError(
                    "Invalid compare operation.".to_string(),
                )),
            },
            Rule::bool_op => match pair_str {
                "==>" => Ok(ir::Op::Bool(ir::BoolOp::Impl)),
                "<==>" => Ok(ir::Op::Bool(ir::BoolOp::Iff)),
                "&&" => Ok(ir::Op::Bool(ir::BoolOp::Conj)),
                "||" => Ok(ir::Op::Bool(ir::BoolOp::Disj)),
                _ => Err(utils::Error::SpecParseError(
                    "Invalid bool operation.".to_string(),
                )),
            },
            Rule::unary_bool_op => match pair_str {
                "!" => Ok(ir::Op::Bool(ir::BoolOp::Neg)),
                _ => Err(utils::Error::SpecParseError(
                    "Invalid unary bool operation.".to_string(),
                )),
            },
            Rule::bit_op => match pair_str {
                "-" => Ok(ir::Op::Bv(ir::BVOp::Sub)),
                "+" => Ok(ir::Op::Bv(ir::BVOp::Add)),
                "&" => Ok(ir::Op::Bv(ir::BVOp::And)),
                "|" => Ok(ir::Op::Bv(ir::BVOp::Or)),
                _ => Err(utils::Error::SpecParseError(
                    "Invalid bitvector operation.".to_string(),
                )),
            },
            _ => Err(utils::Error::SpecParseError(
                "Not an operation.".to_string(),
            )),
        }
    }
}
