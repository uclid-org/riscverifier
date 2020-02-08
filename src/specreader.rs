use std::collections::HashMap;
use std::{cell::RefCell, fs, rc::Rc};

use pest::iterators::Pair;
use pest::Parser;

use crate::DwarfReader;

#[derive(Parser)]
#[grammar = "pest/speclang.pest"]
pub struct SpecReader {
    dwarf_reader: Rc<RefCell<DwarfReader>>,
}

impl SpecReader {
    pub fn create(spec_file_path: &str, dwarf_reader: Rc<RefCell<DwarfReader>>) -> SpecReader {
        let sr = SpecReader { dwarf_reader };
        sr.process_specs_file(spec_file_path);
        sr
    }

    #[allow(dead_code)]
    pub fn process_specs_file(&self, spec_file_path: &str) -> HashMap<String, Vec<String>> {
        let specs_str = fs::read_to_string(spec_file_path)
            .expect("[get_specs] Failed to open specification file.");
        debug!("[get_specs] specs_str: {:#?}", specs_str);
        self.parse_specs(&specs_str[..])
    }

    fn parse_specs(&self, specs_string: &str) -> HashMap<String, Vec<String>> {
        match SpecReader::parse(Rule::func_specs, specs_string) {
            Ok(mut func_specs_pair) => {
                let mut func_specs_inner = func_specs_pair
                    .next()
                    .expect("[parse_specs] Could not find function specifications.")
                    .into_inner();
                let mut function_specs_map = HashMap::new();
                while let Some(spec) = func_specs_inner.next() {
                    let mut spec_inner = spec.into_inner();
                    let spec_pair = spec_inner.next().unwrap();
                    let func_name = SpecReader::get_func_name(spec_pair);
                    let mut function_specs_vec = vec![];
                    while let Some(spec_stmt_pair) = spec_inner.next() {
                        function_specs_vec.push(self.translate_spec_stmt(spec_stmt_pair));
                    }
                    function_specs_map.insert(func_name, function_specs_vec);
                }
                println!("Specs: {:#?}", function_specs_map);
                function_specs_map
            }
            Err(e) => {
                panic!("[get_specs] Specification parsing error: {:?}", e);
            }
        }
    }

    fn get_func_name(pair: Pair<Rule>) -> String {
        match pair.as_rule() {
            Rule::func_name => {
                let mut inner = pair.into_inner();
                let func_name = inner
                    .next()
                    .expect("[get_func_name] The first child should be the function name.")
                    .as_str();
                String::from(func_name)
            }
            _ => panic!("[get_func_name] Not a function_spec rule {:?}.", pair),
        }
    }

    fn translate_spec_stmt(&self, pair: Pair<Rule>) -> String {
        match pair.as_rule() {
            Rule::spec_stmt => {
                let mut spec_stmt_inner = pair.into_inner();
                let spec_type = spec_stmt_inner.next().unwrap().as_str();
                let bool_expr = spec_stmt_inner.next().unwrap();
                // println!("{:#?}", bool_expr);
                format!("{} {}", spec_type, self.translate_expr(bool_expr))
            }
            _ => panic!("[translate_spec_stmt] Not a spec_stmt rule."),
        }
    }

    fn translate_expr(&self, pair: Pair<Rule>) -> String {
        let rule = pair.as_rule();
        let pair_str = pair.as_str();
        let mut inner = pair.into_inner();
        match rule {
            Rule::value_expr
            | Rule::bool_expr
            | Rule::ref_val
            | Rule::get_field
            | Rule::array_index => self.translate_expr(inner.next().unwrap()),
            Rule::ite => {
                let b = self.translate_expr(inner.next().unwrap());
                let c1 = self.translate_expr(inner.next().unwrap());
                let c2 = self.translate_expr(inner.next().unwrap());
                format!("if {} then {} else {}", b, c1, c2)
            }
            Rule::comp_eval | Rule::bool_eval | Rule::bv_eval => {
                let v1 = self.translate_expr(inner.next().unwrap());
                let op = self.translate_expr(inner.next().unwrap());
                let v2 = self.translate_expr(inner.next().unwrap());
                format!("({} {} {})", v1, op, v2)
            }
            Rule::bool_const | Rule::integer => format!("{}", pair_str),
            Rule::path => {
                let mut path = self.translate_expr(inner.next().unwrap());
                while let Some(e) = inner.next() {
                    match e.as_rule() {
                        Rule::array_index => {
                            path =
                                format!("stub_array_index({}, {})", path, self.translate_expr(e));
                        }
                        Rule::get_field => {
                            path = format!("stub_get_field_{}({})", self.translate_expr(e), path);
                        }
                        _ => panic!("[translate_expr] Not a valid path."),
                    }
                }
                path
            }
            Rule::identifier => {
                if self.dwarf_reader.borrow().is_global_var(pair_str) {
                    format!("global_{}()", pair_str)
                } else {
                    format!("{}", pair_str)
                }
            }
            Rule::deref => {
                let ptr = self.translate_expr(inner.next().unwrap());
                format!("deref(mem, {})", ptr)
            }
            Rule::deref_old => {
                let ptr = self.translate_expr(inner.next().unwrap());
                format!("deref(old(mem), {})", ptr)
            }
            Rule::ref_val => {
                let ptr = self.translate_expr(inner.next().unwrap());
                format!("{}", ptr)
            }
            Rule::comp_op => String::from(pair_str),
            _ => panic!("Unsupported rule. {:#?} {:#?}", rule, inner),
        }
    }
}
