#[macro_use]
extern crate log;
extern crate env_logger;

extern crate clap;
use clap::{App, Arg};

extern crate pest;
#[macro_use]
extern crate pest_derive;

mod dwarfreader;
use dwarfreader::DwarfReader;

mod objectdumpparser;
use objectdumpparser::ObjectDumpParser;

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
                .help("RISC-V binary file.")
                .required(true)
                .index(1),
        )
        .get_matches();
    if let Some(binary) = matches.value_of("binary") {
        let binary_paths = vec![String::from(binary)];
        let dr = DwarfReader::create(&binary_paths);
        let assembly_lines = ObjectDumpParser::get_binary_object_dump(&binary_paths);
        
    }
}
