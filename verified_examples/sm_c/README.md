# Keystone's Security Monitor

Verifying Keystone Function Properties (pre/post-condition)

## Getting Started

Install [RISC-V Proxy Kernel and Boot Loader + Keystone SM](https://github.com/keystone-enclave/riscv-pk) and build the security monitor (located in the sm folder; this is only tested with the C implementation) using the Makefile provided.

### Building the Security Monitor

First clone the security monitor repository:
```
git clone https://github.com/keystone-enclave/riscv-pk
cd riscv-pk
```

Then configure:
```
../configure \
        --enable-sm \
        --with-target-platform=default \
        --host=riscv64-unknown-linux-gnu \
        --with-payload=<path to vmlinux>

```

This will generate a makefile, however, the current version of the transalor does not support modeling cyclic call/basic block graphs nor pseudoinstructions. These will have to be removed with some compilation flags. Alternatively, use the Makefile located in this folder which contains added flags to enable compatibility with the translator.

In the future, we plan to read the jump table and enable support for reading pseudoinstructions.

### Generating functions from the security monitor

Refer to [README.md](https://github.com/kkmc/riscverifier/blob/master/README.md).

### Directory explanation

* Makefile: Makefile used to generate the proxy kernel and berkeley boot loader containing the security monitor
* specs: contains the specification files for all the security monitor functions
