use std::collections::HashMap;
use std::fs;

use pest::Parser;
use pest::iterators::Pair;
use pest::iterators::Pairs;

use crate::DwarfReader;

#[derive(Parser)]
#[grammar = "pest/speclang.pest"]
pub struct SpecReader {
}

impl SpecReader {
    pub fn create(spec_file_path: &str) -> SpecReader {
        let mut sr = SpecReader { };
        sr.process_specs_file(spec_file_path);
        sr
    }

    #[allow(dead_code)]
    pub fn process_specs_file(&self, spec_file_path: &str) -> HashMap<String, Vec<String>> {
        let specs_string = fs::read_to_string(spec_file_path)
            .expect("[get_specs] Failed to open specification file.");
        debug!("[get_specs] specs_string: {:#?}", specs_string);
        self.parse_specs(&specs_string[..])
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
                    let function_name = SpecReader::get_function_name(spec_pair);
                    let mut function_specs_vec = vec![];
                    while let Some(spec_stmt_pair) = spec_inner.next() {
                        function_specs_vec.push(SpecReader::translate_spec_stmt(spec_stmt_pair));
                    }
                    function_specs_map.insert(function_name, function_specs_vec);
                }
                println!("Specs: {:#?}", function_specs_map);
                function_specs_map
            }
            Err(e) => {
                panic!("[get_specs] Specification parsing error: {:?}", e);
            }
        }
    }

    fn get_function_name(pair: Pair<Rule>) -> String {
        match pair.as_rule() {
            Rule::func_name => {
                let mut inner = pair.into_inner();
                let function_name = inner
                    .next()
                    .expect("[get_function_name] The first child should be the function name.")
                    .as_str();
                String::from(function_name)
            }
            _ => panic!("[get_function_name] Not a function_spec rule {:?}.", pair),
        }
    }

    fn translate_spec_stmt(pair: Pair<Rule>) -> String {
        match pair.as_rule() {
            Rule::spec_stmt => {
                let mut spec_stmt_inner = pair.into_inner();
                let spec_type = spec_stmt_inner.next().unwrap().as_str();
                let bool_expr = spec_stmt_inner.next().unwrap();
                format!("{} {}", spec_type, SpecReader::translate_expr(bool_expr))
            }
            _ => panic!("[translate_spec_stmt] Not a spec_stmt rule."),
        }
    }

    fn translate_expr(pair: Pair<Rule>) -> String {
        let rule = pair.as_rule();
        let mut inner = pair.into_inner();
        match rule {
            Rule::bool_expr | Rule::path_expr | Rule::ref_val => {
                SpecReader::translate_expr(inner.next().unwrap())
            },
            Rule::ite => {
                let b = SpecReader::translate_expr(inner.next().unwrap());
                let c1 = SpecReader::translate_expr(inner.next().unwrap());
                let c2 = SpecReader::translate_expr(inner.next().unwrap());
                format!("if {} then {} else {}", b, c1, c2)
            },
            Rule::comp_eval | Rule::bool_eval | Rule::bv_eval => {
                let v1 = SpecReader::translate_expr(inner.next().unwrap());
                let op = SpecReader::translate_expr(inner.next().unwrap());
                let v2 = SpecReader::translate_expr(inner.next().unwrap());
                format!("({} {} {})", v1, op, v2)
            },
            Rule::bool_const | Rule::integer | Rule::identifier => {
                format!("{}", inner.next().unwrap().as_str())
            },
            Rule::path_expr_list => {
                let mut rev_inner = inner.rev();
                let mut path_string = String::from("");
                while let Some(path_expr) = rev_inner.next() {
                    let path_expr_string = SpecReader::translate_expr(path_expr);
                    // format!("")
                }
                String::from("")
            },
            Rule::array_index => {
                let array_id = SpecReader::translate_expr(inner.next().unwrap());
                let index = SpecReader::translate_expr(inner.next().unwrap());
                // FIXME: Need to get type from typemap
                format!("{}_array_index({})", array_id, index)
            },
            // Rule::deref => {
                
            // }
            _ => panic!("Unsupported rule. {:?}", rule),
        }
    }
}
