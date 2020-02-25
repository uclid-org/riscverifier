#!/bin/bash
# Binary folder
if [ -d bin ]; then
    rm -rf bin
fi
if [ ! -d bin ]; then
    mkdir bin
fi
for cfile in "c"/*.c; do
    #$(riscv64-unknown-elf-gcc $cfile -g -gdwarf -o bin/$(basename -- ${cfile%.c}).out -march=rv64g -fno-jump-tables -nostdlib -nostartfiles -Tbbl.lds)
    $(riscv64-unknown-elf-gcc $cfile -g -gdwarf -o bin/$(basename -- ${cfile%.c}).out -march=rv64g -mabi=lp64d -fno-jump-tables -nostdlib -nostartfiles -Tbbl.lds)
done
