#[macro_use]
extern crate log;
extern crate env_logger;

#[macro_use]
extern crate lalrpop_util;
lalrpop_mod!(pub riscv_spec_lang, "/spec_lang/riscv_spec_lang.rs"); // synthesized by LALRPOP

extern crate clap;
use clap::{App, Arg};

extern crate pest;
#[macro_use]
extern crate pest_derive;

extern crate topological_sort;

use std::collections::HashSet;
use std::fs::File;
use std::io::prelude::*;
use std::rc::Rc;

mod dwarf_interfaces;
use dwarf_interfaces::cdwarfinterface::CDwarfInterface;

mod readers;
use readers::disassembler::Disassembler;
use readers::dwarfreader::DwarfReader;

mod spec_lang;
use spec_lang::sl_parser;

mod translator;
use translator::Translator;

mod verification_interfaces;
use verification_interfaces::uclidinterface::Uclid5Interface;

mod datastructures;
use datastructures::cfg::BasicBlock;

mod system_model;

mod ast;

mod ir_interface;

mod utils;

fn main() {
    env_logger::init();
    let matches = App::new("RISCVerifier")
        .version("1.0")
        .author("Kevin Cheang <kcheang@berkeley.edu>")
        .about("Translates RISC-V assembly (support for 64g only) programs into an IR")
        .arg(
            Arg::with_name("binaries")
                .short("b")
                .long("binary")
                .help("RISC-V binary file.")
                .required(true)
                .index(1),
        )
        .arg(
            Arg::with_name("modname")
                .short("n")
                .long("modname")
                .help("UCLID module name")
                .required(false)
                .takes_value(true),
        )
        .arg(
            Arg::with_name("spec")
                .short("s")
                .long("spec")
                .help("RISC-V specification file.")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("output")
                .help("Specify the output path.")
                .short("o")
                .long("output")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("function")
                .help("Specify a list of functions to verify.")
                .short("f")
                .long("function")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("xlen")
                .help("Specify the architecture XLEN.")
                .short("x")
                .long("xlen")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("ignore-funcs")
                .help("Comma separated list of functions to ignore. E.g. \"foo,bar\"")
                .short("i")
                .long("ignore-funcs")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("verify-funcs")
                .help("List of functions to verify.")
                .short("v")
                .long("verify-funcs")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("ignore-specs")
                .help("List of functions to verify.")
                .long("ignore-specs")
                .takes_value(false),
        )
        .get_matches();
    let xlen = utils::dec_str_to_u64(matches.value_of("xlen").unwrap_or("64"))
        .expect("[main] Unable to parse numberic xlen.");
    if xlen != 64 {
        warn!("uclidinterface is hard-coded with 64 bit dependent definitions.");
        panic!("[main] Non-64 bit XLEN is not yet implemented.");
    }
    // Parse function blocks from binary
    let binary_paths = matches
        .value_of("binaries")
        .map_or(vec![], |lst| lst.split(",").collect::<Vec<&str>>());
    // Disassemble binaries and create basic blocks
    let mut disassembler = Disassembler::new(None, Some("debug_log"));
    let als = disassembler.read_binaries(&binary_paths);
    let bbs = BasicBlock::split(&als);
    // Module name
    let module_name = matches.value_of("modname").unwrap_or("main");
    // Initialize DWARF reader
    let dwarf_reader: Rc<DwarfReader<CDwarfInterface>> =
        Rc::new(DwarfReader::new(&xlen, &binary_paths).unwrap());
    // Function to generate
    let func_names = matches
        .value_of("function")
        .map_or(vec![], |lst| lst.split(",").collect::<Vec<&str>>());
    // Specification
    let spec_parser = sl_parser::SpecParser::new(xlen, dwarf_reader.ctx());
    let spec_files = matches
        .value_of("spec")
        .map_or(vec![], |lst| lst.split(",").collect::<Vec<&str>>());
    let specs_map = spec_parser
        .process_spec_files(&spec_files)
        .expect("Could not read spec.");
    // Get ignored functions
    let ignored_funcs = matches
        .value_of("ignore-funcs")
        .map_or(HashSet::new(), |lst| {
            lst.split(",").collect::<HashSet<&str>>()
        });
    // Get list of functions to verify
    let verify_funcs = matches
        .value_of("verify-funcs")
        .map_or(vec![], |lst| lst.split(",").collect::<Vec<&str>>());
    // Flag for ignoring and inlining functions
    let ignore_specs = matches.is_present("ignore-specs");
    // Translate and write to output file
    let mut translator: Translator<Uclid5Interface> = Translator::new(
        xlen,
        &module_name,
        &bbs,
        &ignored_funcs,
        &verify_funcs,
        dwarf_reader.ctx(),
        &specs_map,
        ignore_specs,
    );
    for func_name in func_names {
        translator.gen_func_model(&func_name);
    }
    // Print model to file
    let model_str = translator.print_model();
    if let Some(output_file) = matches.value_of("output") {
        let res = File::create(output_file)
            .ok()
            .unwrap()
            .write_all(model_str.as_bytes());
        match res {
            Ok(_) => (),
            Err(_) => panic!("Unable to write model to {}", output_file),
        }
    }
    translator.clear();
}
