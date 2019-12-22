#[macro_use]
extern crate log;
extern crate env_logger;
extern crate clap;

use clap::{App, Arg};

mod dwarfreader;

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
        // .arg(
        //     Arg::with_name("dwarfdump")
        //     .multiple(true)
        //     .help("Turn on dwarf dump."),
        // )
        .get_matches();
    if let Some(binary) = matches.value_of("binary") {
        let binary_paths = vec![String::from(binary)];
        let dr = dwarfreader::DwarfReader::create(binary_paths);
        println!("function addr: {:?}", dr.get_function_formal_argument_names("pmp_detect_region_overlap_atomic"));
    }
}
