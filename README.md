# BRAVE (Berkeley RISC-V Assembly Verifier for Enclaves)

A translator from RISC-V binary to Uclid5.

# Installation

## Pre-requisites

You will need to install [Uclid5](https://github.com/uclid-org/uclid) (note that it needs to be Pranav's branch where the old operator in ensures statements are fixed -- Jan.6.2020) and riscv-gnu-toolchain from [riscv](https://github.com/riscv). Make sure you have an alias to the riscv disassembler (riscv64-unknown-elf-objdump).

## Building the project

To build the project, run:

`cargo build`

# RISC-V Assembly Uclid5 models

## Generating Uclid5 models

To generate a model of a function in a binary, run the following command:

`./target/debug/riscverifier /path/to/binary -f function_to_verify -o output_filename.ucl -i ignored,functions,list`

This will generate a Uclid5 model of the function in assembly by recursively finding all the functions called by function\_to\_verify, generate a procedure for each, including its basic blocks, but ignore the functions specified by the -i flag. The ignored functions are replaced by a stub Uclid5 procedure.

## Running the generated models and scalability

Remember to run with Boolector or CVC4 or else these models may take forever to verify. Note that there are no quantifiers in any of these generated models; it uses the logic QF\_AUFBV (Jan.6.2020), where UF is required for multiplication in indexing. The option for Uclid5 to run with the external solver CVC4 is:

`uclid -s "cvc4 --incremental --lang smt2 --force-logic=ALL" model.ucl`

You may replace ALL with a more restrictive logic.

Example:

`time RUST_BACKTRACE=1 RUST_LOG="debug" ./target/debug/riscverifier ~/workspace/uclid5/riscvtest/test_bin/test-struct-2.out -f main -s Foo,Bar -a Foo,int -o /Users/kcheang/workspace/riscverifier/testingoutput2 2>&1 | less`

## Notes

Jan 6th 2020
* Adding support for global variables including primitive, array, and struct types
* Adding support for specification language

Jan 4th 2020
* Added condition for correct return "ensures (pc == old(ra)[63:1] ++ 0bv1);"
* Moved old\_mem == mem constraint to assumption at the beginning of functions
* Added verify for each procedure in control block (commented out), e.g.
    * f1 = verify(function1);
	* fn = verify(functionn);
	* check;
	* print\_results;
* Assumptions added: ensures (pc == old(ra)[63:1] ++ 0bv1) if ra is modified or (pc == ra[63:1] ++ 0bv1) if it isn't. 

## TODO

* Support for floating point registers
