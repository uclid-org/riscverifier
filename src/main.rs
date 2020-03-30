#[macro_use]
extern crate log;
extern crate env_logger;

extern crate clap;
use clap::{App, Arg};

extern crate pest;
#[macro_use]
extern crate pest_derive;

extern crate topological_sort;

use std::collections::{HashMap, HashSet};
use std::rc::Rc;

mod dwarf_interfaces;
use dwarf_interfaces::cdwarfinterface::CDwarfInterface;

mod readers;
use readers::disassembler::Disassembler;
use readers::dwarfreader::DwarfReader;
use readers::objectdumpreader::ObjectDumpReader;
use readers::specreader::SpecReader;

mod translator;
use translator::Translator;

mod verification_interfaces;
use verification_interfaces::uclidinterface::Uclid5Interface;

mod datastructures;
use datastructures::cfg::{BasicBlock, Cfg};

mod ir;

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
    let function_blocks = ObjectDumpReader::get_binary_object_dump(&binary_paths);

    // TEST
    let mut disassembler = Disassembler::new(None, Some("debug_log"));
    let als = disassembler.read_binaries(&binary_paths);
    // println!("{:#?}", als);
    // println!("{:#?}", BasicBlock::split(&als));
    // println!("{:#?}", Cfg::new(2147483652, &als));
    // return;

    // Module name
    let module_name = matches.value_of("modname").unwrap_or("main");
    // Get ignored functions
    let ignored_functions = matches
        .value_of("ignore-funcs")
        .map_or(HashSet::new(), |lst| {
            lst.split(",").collect::<HashSet<&str>>()
        });
    // Initialize DWARF reader
    let dwarf_reader: Rc<DwarfReader<CDwarfInterface>> =
        Rc::new(DwarfReader::new(&xlen, &binary_paths).unwrap());
    // Function to generate
    let func_names = matches
        .value_of("function")
        .map_or(vec![], |lst| lst.split(",").collect::<Vec<&str>>());
    // Specification
    let spec_reader = SpecReader::new(xlen, dwarf_reader.ctx());
    let spec_files = matches
        .value_of("spec")
        .map_or(vec![], |lst| lst.split(",").collect::<Vec<&str>>());
    let specs_map = spec_reader
        .process_specs_files(&spec_files)
        .expect("Could not read spec.");
    // Translate and write to output file
    let mut func_blks = HashMap::new();
    for (k, v) in function_blocks {
        let blk = v.iter().map(|al| Rc::new(al.clone())).collect::<Vec<_>>();
        let cfg = Rc::new(ObjectDumpReader::get_cfg(blk.clone()));
        func_blks.insert(format!("{}", k), Rc::clone(&cfg));
        func_blks.insert(blk[0].function_name().to_string(), Rc::clone(&cfg));
    }
    let mut translator: Translator<Uclid5Interface> = Translator::new(
        xlen,
        &module_name,
        &func_blks,
        &ignored_functions,
        dwarf_reader.ctx(),
        &specs_map,
    );
    for func_name in func_names {
        translator
            .gen_func_model(&func_name)
            .expect("Unable to generate function model.");
    }
    translator.print_model();
}
