# VERI-V

An instruction level translator for RISC-V binaries.

# Installation

## Pre-requisites

The current version of the translator uses a Uclid5 interface for modeling. To use this, you will need to install [Uclid5](https://github.com/uclid-org/uclid) (use the experimental-modifies branch where the old operator in the ensures statements are fixed -- Feb.24.2020) and riscv-gnu-toolchain from [riscv](https://github.com/riscv). Make sure you have an alias to the riscv disassembler (riscv64-unknown-elf-objdump).

## Building the project

To build the project, run:

`cargo build`

# RISC-V Assembly Uclid5 models

## Generating Uclid5 models

To generate a model of a function in a binary, run the following command:

`./target/debug/riscverifier /path/to/binary -f function_to_verify -o output_filename.ucl -i ignored,functions,list`

This will generate a Uclid5 model of the function in assembly by recursively finding all the functions called by function\_to\_verify, generate a procedure for each, including its basic blocks, but ignore the functions specified by the -i flag. The ignored functions are replaced by a stub Uclid5 procedure.

## Running the generated models and scalability

Running with Boolector or CVC4 is best. Note that there are no quantifiers in any of these generated models; it uses the logic QF\_ABV (Feb.24.2020). The option for Uclid5 to run with the external solver CVC4 is:

`uclid -s "cvc4 --incremental --lang smt2 --force-logic=ALL" model.ucl`

Example:

`RUST_BACKTRACE=1 RUST_LOG="debug" ./target/debug/riscverifier ~/workspace/uclid5/riscvtest/test_bin/test-struct-2.out -f main -o /Users/kcheang/workspace/riscverifier/testingoutput2 2>&1 | less`

UPDATE: Currently, the SMTLIB interface in Uclid5 is broken and the models will not run due to a stack overflow bug.

## TODO

* [ ] Add option to manually specify the modifies set
* [ ] Add deref and ref in specification language
* [ ] Write spec language (syntax and semantics) document
* [ ] Support for floating point registers

Stretch goals:
* [ ] Reimplement the dissasembler (after my PhD :-)).

## Notes

Feb 25 2020
* [ ] Verify pmp\_set in the security monitor

Feb 24 2020
* [x] Re-factored the code; there is a general translator for all DWARF formats and verification IRs/languages. Implemented a C DWARF parser and Uclid5 interface.
* [x] Automatically inferrs the global variables and macro helper functions for array indexing and struct field operations via globals and function arguments.
* [x] Implemented a specification language that is automatically translated.

Jan 6th 2020
* [x] Adding support for global variables including primitive, array, and struct types
* [x] Adding support for specification language

Jan 4th 2020
* [x] Added condition for correct return "ensures (pc == old(ra)[63:1] ++ 0bv1);"
* [x] Moved old\_mem == mem constraint to assumption at the beginning of functions
* [x] Added verify for each procedure in control block (commented out), e.g.
    * f1 = verify(function1);
	* fn = verify(functionn);
	* check;
	* print\_results;
* [x] Assumptions added: ensures (pc == old(ra)[63:1] ++ 0bv1) if ra is modified or (pc == ra[63:1] ++ 0bv1) if it isn't. 


