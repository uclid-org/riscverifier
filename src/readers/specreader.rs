use std::collections::{HashMap, HashSet};
use std::fs;

use pest::iterators::Pair;
use pest::Parser;

use crate::ir;
use crate::readers::dwarfreader::DwarfCtx;
use crate::system_model;
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

    pub fn process_specs_files(
        &self,
        spec_file_paths: &Vec<&str>,
    ) -> Result<HashMap<String, Vec<ir::Spec>>, utils::Error> {
        let mut specs_map = HashMap::new();
        for spec_file_path in spec_file_paths {
            specs_map.extend(self.process_specs_file(spec_file_path)?);
        }
        Ok(specs_map)
    }

    /// Reads the specification file and parses the text within the file. Returns a map of function names to list of sepcs (ir::Spec)
    pub fn process_specs_file(
        &self,
        spec_file_path: &str,
    ) -> Result<HashMap<String, Vec<ir::Spec>>, utils::Error> {
        let specs_str = match fs::read_to_string(spec_file_path) {
            Ok(res) => res,
            Err(e) => panic!("Failed to read spec file: {}. {}", spec_file_path, e),
        };
        self.parse_specs(&specs_str[..])
    }

    /// Parses the specification file text and returns a map of functions to list of spec (ir::Spec)
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

    /// Given the func_name rule, returns the function name
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

    /// Given a spec_stmt rule, returns a ir::Spec corresponding to the specification string
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

    /// Translates modifies set into ir
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
        self._translate_expr(func_name, pair, &mut HashMap::new())
    }
    /// Trnaslates an expression to ir
    fn _translate_expr(
        &self,
        func_name: &str,
        pair: Pair<Rule>,
        bound_var_map: &mut HashMap<String, ir::Expr>,
    ) -> Result<ir::Expr, utils::Error> {
        let rule = pair.as_rule();
        let pair_str = pair.as_str();
        let mut inner = pair.into_inner();
        match rule {
            Rule::old => {
                let inner_expr =
                    self._translate_expr(func_name, inner.next().unwrap(), bound_var_map)?;
                Ok(ir::Expr::op_app(ir::Op::Old, vec![inner_expr]))
            }
            Rule::value_expr | Rule::bool_expr | Rule::get_field | Rule::array_index => {
                self._translate_expr(func_name, inner.next().unwrap(), bound_var_map)
            }
            Rule::comp_eval | Rule::bool_eval | Rule::bv_eval => {
                let v1 = self._translate_expr(func_name, inner.next().unwrap(), bound_var_map)?;
                let op = self.translate_op(inner.next().unwrap())?;
                let v2 = self._translate_expr(func_name, inner.next().unwrap(), bound_var_map)?;
                Ok(ir::Expr::op_app(op, vec![v1, v2]))
            }
            Rule::unary_bool_eval => {
                let op = self.translate_op(inner.next().unwrap())?;
                let v = self._translate_expr(func_name, inner.next().unwrap(), bound_var_map)?;
                Ok(ir::Expr::op_app(op, vec![v]))
            }
            Rule::bool_const => Ok(ir::Expr::bool_lit(pair_str == "true")),
            Rule::integer => Ok(ir::Expr::bv_lit(
                utils::dec_str_to_i64(pair_str).unwrap() as u64,
                self.xlen,
            )),
            Rule::bitvec => {
                let mut iter = pair_str.split("bv");
                let val_str = iter.next().unwrap();
                let val = if val_str.len() > 2 && &val_str[0..2] == "0x" {
                    utils::hex_str_to_u64(&val_str[2..]).unwrap()
                } else {
                    utils::dec_str_to_u64(&val_str).unwrap()
                };
                let width = utils::dec_str_to_u64(iter.next().unwrap()).unwrap();
                Ok(ir::Expr::bv_lit(val, width))
            }
            Rule::path | Rule::path_ref => {
                let path_ref = rule == Rule::path_ref;
                let mut path =
                    self._translate_expr(func_name, inner.next().unwrap(), bound_var_map)?;
                // Check if it's a function reference (which is assumed to be a variable during the first translation pass)
                if path_ref
                    && path.is_var()
                    && self.dwarf_ctx.func_sig_exists(&path.get_expect_var().name)
                {
                    let id = &path.get_expect_var().name;
                    let func_app_name = utils::global_func_addr_name(id);
                    return Ok(ir::Expr::func_app(
                        func_app_name,
                        vec![],
                        ir::Type::Bv { w: self.xlen },
                    ));
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
                // FIXME: Fix how memory is translated
                let is_mem = path.get_expect_var().name == system_model::MEM_VAR;
                while let Some(e) = inner.next() {
                    match e.as_rule() {
                        Rule::array_index => {
                            path = ir::Expr::op_app(
                                ir::Op::ArrayIndex,
                                vec![path, self._translate_expr(func_name, e, bound_var_map)?],
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
                if !path_ref && (is_global_var || is_ptr_type || is_mem) {
                    path = ir::Expr::op_app(
                        ir::Op::Deref(path.typ().get_expect_bv_width()),
                        vec![path],
                    );
                }
                Ok(path)
            }
            Rule::f_app => {
                let f_name_pair = inner.next().unwrap();
                let f_name = match &f_name_pair.as_rule() {
                    Rule::identifier => f_name_pair.as_str(),
                    _ => panic!("Function application should have an identifier as name."),
                };
                let mut expr_args = vec![];
                while let Some(arg) = inner.next() {
                    expr_args.push(self._translate_expr(func_name, arg, bound_var_map)?);
                }
                match f_name {
                    "bv_sign_extend" => {
                        expr_args.reverse();
                        Ok(ir::Expr::op_app(ir::Op::Bv(ir::BVOp::SignExt), expr_args))
                    },
                    "bv_zero_extend" => {
                        expr_args.reverse();
                        Ok(ir::Expr::op_app(ir::Op::Bv(ir::BVOp::ZeroExt), expr_args))
                    },
                    _ => panic!("Unimplemented function application in specreader."),
                }
            }
            Rule::identifier => {
                // If it's a quantifier bound variable, return the expression from the map
                if let Some(v) = bound_var_map.get(pair_str) {
                    return Ok(v.clone());
                }
                // Identifiers preceeding with a $ are special symbols in the specification language
                // Either the symbol is a system state variable
                // or a return value of the function
                if pair_str.starts_with("$") {
                    let suffix = &pair_str[1..];
                    // System variable
                    if system_model::SYSTEM_VARS.contains(&suffix) {
                        return Ok(ir::Expr::var(
                            suffix,
                            system_model::system_var_type(suffix, self.xlen),
                        ));
                    }
                    // Function return value
                    if suffix == "ret" {
                        let ret_typ = self.dwarf_ctx
                            .func_sig(func_name)?
                            .ret_type
                            .clone()
                            .and_then(|typ| Some(typ.to_ir_type()))
                            .expect("Unable to determine type for return value or function does not return a value.");
                        return Ok(ir::Expr::var("$ret", ret_typ));
                    }
                }
                // Look for variable in global variables
                let mut typ = self
                    .dwarf_ctx
                    .global_var(pair_str)
                    .and_then(|v| Ok(v.typ_defn.clone()));
                // Look for variable in function argument
                if typ.is_err() {
                    let arg = self
                        .dwarf_ctx
                        .func_sig(func_name)?
                        .args
                        .iter()
                        .find(|v| v.name == pair_str)
                        .expect(&format!(
                            "Variable {} is also not a function argument.",
                            pair_str
                        ));
                    typ = Ok(arg.typ_defn.clone());
                }
                Ok(ir::Expr::var(
                    pair_str,
                    typ.expect("Unable to find variable.").to_ir_type(),
                ))
            }
            Rule::quantified_expr => {
                let quant_type = inner.next().unwrap().as_str();
                let name = inner.next().unwrap().as_str().to_string();
                let typ = self.translate_typ(inner.next().unwrap())?;
                let bound_var = ir::Var {
                    name: name.clone(),
                    typ: typ.clone(),
                };
                bound_var_map.insert(name.clone(), ir::Expr::Var(bound_var.clone(), typ.clone()));
                let b_expr =
                    self._translate_expr(func_name, inner.next().unwrap(), bound_var_map)?;
                match quant_type {
                    "forall" => Ok(ir::Expr::op_app(ir::Op::Forall(bound_var), vec![b_expr])),
                    "exists" => Ok(ir::Expr::op_app(ir::Op::Exists(bound_var), vec![b_expr])),
                    _ => panic!(
                        "Invalid quantifier. A quantifier is either a 'forall' or an 'exists'."
                    ),
                }
            }
            _ => panic!("Unsupported rule. {:#?} {:#?}", rule, inner),
        }
    }

    /// Translates type definitions to ir
    fn translate_typ(&self, pair: Pair<Rule>) -> Result<ir::Type, utils::Error> {
        let rule = pair.as_rule();
        let pair_str = pair.as_str();
        match rule {
            Rule::typ => {
                if pair_str.contains("bv") {
                    let mut iter = pair_str.split("bv");
                    iter.next();
                    let val_str = iter.next().unwrap();
                    Ok(ir::Type::Bv {
                        w: utils::dec_str_to_u64(val_str).expect("Invalid bv type width."),
                    })
                } else {
                    panic!("Invalid type {} or translation not supported.", pair_str)
                }
            }
            _ => Err(utils::Error::SpecParseError(
                "Could not translate non-type pair.".to_string(),
            )),
        }
    }

    /// Translates an operator to ir
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
                "++" => Ok(ir::Op::Bv(ir::BVOp::Concat)),
                "<<" => Ok(ir::Op::Bv(ir::BVOp::LeftShift)),
                ">>" => Ok(ir::Op::Bv(ir::BVOp::RightShift)),
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
