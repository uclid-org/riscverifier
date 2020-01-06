# RISC-Verifier
A translator from RISC-V binary to Uclid5.

#Installation

## Pre-requisites

You will need to install [Uclid5](https://github.com/uclid-org/uclid) (note that it needs to be Pranav's branch where the old operator in ensures statements are fixed -- Jan.6.2020) and riscv-gnu-toolchain from [riscv](https://github.com/riscv). Make sure you have an alias to the riscv disassembler (riscv64-unknown-elf-objdump). To generate a model of a function in a binary, run the following command:

`./target/debug/riscverifier /path/to/binary -f function_to_verify -o output_filename.ucl -i ignored,functions,list`

This will generate a Uclid5 model of the function in assembly by recursively finding all the functions called by function\_to\_verify, generate a procedure for each, including its basic blocks, but ignore the functions specified by the -i flag. The ignored functions are replaced by a stub Uclid5 procedure.

## Generating uclid5 models

WIP

## Notes

Jan 6th 2020
* Adding support for global variables including primitive, array, and struct types
* Adding support for specification language

Jan 4th 2020
* Added condition for correct return "ensures (pc == old(ra)[63:1] ++ 0bv1);"
* Moved old_mem == mem constraint to assumption at the beginning of functions
* Added verify for each procedure in control block (commented out), e.g.
** f1 = verify(function1);
** fn = verify(functionn);
** check;
** print_results;
* Assumptions added: ensures (pc == old(ra)[63:1] ++ 0bv1) if ra is modified or (pc == ra[63:1] ++ 0bv1) if it isn't. Add into procedure body tmp_ra = ra, and then pc = tmp_ra[63:1] ++ 0bv1 so this passes. Also assign memory to old_mem at the end of the function procedure and ensure (mem == old(mem)). These assumptions are used to restore the stack frame after a call. May need to use temporary variables for other registers that need to be preserved across call frames.

## TODO

Jan 4th 2020
* Fix the addr / rs + imm in prelude so it's consistent
