use std::fs;
use std::collections::{HashMap};

use pest::Parser;

#[derive(Parser)]
#[grammar = "pest/speclang.pest"]
pub struct SpecReader;

impl SpecReader {
	#[allow(dead_code)]
	pub fn get_specs(spec_file_path: &str) -> HashMap<String, Vec<String>> {
		let specs_string = fs::read_to_string(spec_file_path).expect("[get_specs] Could not read specification.").replace("\t", " ");
		debug!("[get_specs] specs_string: {:#?}", specs_string);
        match SpecReader::parse(Rule::function_specs, &specs_string[..]) {
        	Ok(_pest_object) => {
		        println!("specs: {:#?}", _pest_object);
        		HashMap::new()
        	}
        	Err(e) => {
        		panic!("Could not parse. {:?}", e);
        	},
        }
	}
}