# VERIV

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

`./target/debug/riscverifier /path/to/binary -f function_to_verify -i ignored,functions,list -o outputfile.ucl`

This will generate a Uclid5 model of the function in assembly by recursively finding all the functions called by function\_to\_verify, generate a procedure for each, including its basic blocks, but ignore the functions specified by the -i flag. The ignored functions are replaced by a stub Uclid5 procedure.

## Running the generated models and scalability

Note that the base models without specifications have no quantifiers. The SMT models are in QF\_ABV (June.7.2020). The option for Uclid5 to run with the external solver is -s. For example:

`uclid -s "cvc4 --incremental --lang smt2 --force-logic=ALL" model.ucl`

Example:

To recompile and run VERIV:

`cargo run ~/workspace/verification/build/sm.build/bbl -f pmp_set -i printm,poweroff -s spec_file.rvspecs -o output.ucl`

To run with the built binary:

`./target/debug/riscverifier ~/workspace/verification/veriv/build/sm.build/bbl -f pmp_set -i poweroff,printm -s spec_file.rvspecs -o output.ucl`

To turn on debugging, prefix the commands above with RUST\_LOG="debug" (or whichever level of debugging you prefer).

## Specification Language

The -s option allows the user to write a C-like specification that is then translated to the RV binary level.

For references, here is an informal grammar description:

```
# := number
<SpecFile> := <FuncSpec>*
<Ident> := r"\w([0-9]\w)*" (alphanumeric identifier starting with an alphabet)
<FuncSpec> := 'fun' <Ident> '{' <Spec>* '}'
<Spec> := 'ensures' <BExpr> ';' |
          'requires' <BExpr> ';' |
          'modifies' <Ident>* ';'
<BExpr> := <BExpr2> <InfixBoolOp> <BExpr> |
           <PrefixBoolOp> <BExpr> |
           <*>? <VExpr> <CompOp> <*>? <VExpr> |
           <BExpr2>
<BExpr2> := 'true' | 'false' | '(' <BExpr> ')'
<VarDecl> := <Ident> ':' <TypeDecl>
<TypeDecl> := 'bv#'                     // (e.g. bv64)
<InfixBoolOp> := '||' | '&&' | '==>'
<PrefixBoolOp> := '!' |
                  'forall' '(' VarDecl ')' '::' |
                  'exists' '(' VarDecl ')' '::'
<CompOp> := '>' | '<' | '>_u' | '<_u' |
            '>=' | '<=' | '>=_u' | '<=_u'
<VExpr> := <VExpr> <ValueOp1> <VExpr2> |
           <VExpr> '[' <VExpr> ']' |    // (array index)
           <VExpr> '.' <Ident> |        // (struct get field)
           <VExpr> '[' # ':' # ']'      // (slicing; e.g. [0:31])
           <VExpr2>
<ValueOp1> := '+' | '-' | '^' | '&' | '|'
<VExpr2> := <VExpr2> <ValueOp2> <Term> |
            <Term>
<ValueOp2> := '/' | '*' | '>>' | '>>>' | '<<'
<Term> := '$tt' | '$ff' | # | #bv# | 'old(' <VExpr> ')' | <Ident>
```

## TODO

* VERY OUT OF DATES DO NOT REFER TO THE NOTES BELOW

* [ ] Handle indirect jumps?
* [ ] Separate the data and stack memory sections into mem\_stack and mem\_data
* [ ] Add forall into the specificaiton language 

* [X] Add option to manually specify the modifies set
* [X] Add deref and ref in specification language
* [ ] Write spec language (syntax and semantics) document
* [ ] Support for floating point registers

## Notes

Mar 4 2022
* For RISC-V architectures, use the following options for debugging information and the base instruction set: `-g -gdwarf -fno-jump-tables -march=rv64imafd -mabi=lp64d`

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


