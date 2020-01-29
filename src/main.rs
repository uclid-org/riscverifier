#[macro_use]
extern crate log;
extern crate env_logger;

extern crate clap;
use clap::{App, Arg};

extern crate pest;
#[macro_use]
extern crate pest_derive;

extern crate topological_sort;

use std::collections::HashSet;

mod dwarfreader;
use dwarfreader::DwarfReader;

mod objectdumpreader;
use objectdumpreader::ObjectDumpReader;

// mod specreader;
// use specreader::SpecReader;

mod uclidtranslator;
use uclidtranslator::UclidTranslator;

mod context;

mod utils;

fn main() {
    env_logger::init();
    let matches = App::new("RISCVerifier")
        .version("1.0")
        .author("Kevin Cheang <kcheang@berkeley.edu>")
        .about("Translates RISC-V assembly (support for 64g only) programs into an IR")
        .arg(
            Arg::with_name("binary")
                .short("b")
                .long("binary")
                .help("RISC-V binary file.")
                .required(true)
                .index(1),
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
                .help("Specify a function to verify.")
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
            Arg::with_name("struct-macros")
                .help("Comma separated list of struct ids to generate operator macros for. E.g. \"enclave\"")
                .short("m")
                .long("struct-macros")
                .takes_value(true),
        )
        .arg(
            Arg::with_name("array-macros")
            .help("Comma separated list of type definitions to generate operator macros for.")
            .short("a")
            .long("array-macros")
            .takes_value(true),
        )
        .get_matches();
    let xlen = utils::dec_str_to_u64(matches.value_of("xlen").unwrap_or("64"))
        .expect("[main] Unable to parse numberic xlen.");
    if xlen != 64 {
        warn!("[main] Non-64 bit XLEN is not yet tested. Use with caution.");
    }
    if let Some(binary) = matches.value_of("binary") {
        let binary_paths = vec![String::from(binary)];  // FIXME: Handle multiple binaries
        let function_blocks = ObjectDumpReader::get_binary_object_dump(&binary_paths);
        let mut ignored_functions = HashSet::new();
        if let Some(ignore_list_str) = matches.value_of("ignore-funcs") {
            ignored_functions = ignore_list_str.split(",").collect::<HashSet<&str>>();
        }
        let mut struct_macro_ids = HashSet::new();
        if let Some(struct_macro_list_str) = matches.value_of("struct-macros") {
            struct_macro_ids = struct_macro_list_str.split(",").collect::<HashSet<&str>>();
        }
        let mut array_macro_ids = HashSet::new();
        if let Some(array_macro_list_str) = matches.value_of("array-macros") {
            array_macro_ids = array_macro_list_str.split(",").collect::<HashSet<&str>>();
        }
        // let specs = matches.value_of("spec").map_or_else(|| None, |v| Some(SpecReader::get_specs(v)));
        let mut dwarf_reader = DwarfReader::create(xlen, &binary_paths);
        if let Some(write_to_filepath) = matches.value_of("output") {
            if let Some(function_name) = matches.value_of("function") {
                let mut ut = UclidTranslator::create(
                    xlen,
                    &mut dwarf_reader,
                    &ignored_functions,
                    &struct_macro_ids,
                    &array_macro_ids,
                    &function_blocks,
                );
                ut.generate_function_model(function_name)
                    .expect("[main] Unable to generate model for function");
                ut.write_model(&write_to_filepath)
                    .expect("[main] Unable to write model to file.");
                ut.reset_model();
            }
        }
    }
}
