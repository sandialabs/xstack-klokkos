KLEE Symbolic Virtual Machine
=============================

[![Build Status](https://github.com/klee/klee/workflows/CI/badge.svg)](https://github.com/klee/klee/actions?query=workflow%3ACI)
[![Build Status](https://api.cirrus-ci.com/github/klee/klee.svg)](https://cirrus-ci.com/github/klee/klee)
[![Coverage](https://codecov.io/gh/klee/klee/branch/master/graph/badge.svg)](https://codecov.io/gh/klee/klee)

`KLEE` is a symbolic virtual machine built on top of the LLVM compiler
infrastructure. Currently, there are two primary components:

  1. The core symbolic virtual machine engine; this is responsible for
     executing LLVM bitcode modules with support for symbolic
     values. This is comprised of the code in lib/.

  2. A POSIX/Linux emulation layer oriented towards supporting uClibc,
     with additional support for making parts of the operating system
     environment symbolic.

Additionally, there is a simple library for replaying computed inputs
on native code (for closed programs). There is also a more complicated
infrastructure for replaying the inputs generated for the POSIX/Linux
emulation layer, which handles running native programs in an
environment that matches a computed test input, including setting up
files, pipes, environment variables, and passing command line
arguments.

For further information, see the [webpage](http://klee.github.io/)
and this repositories [wiki](https://github.gatech.edu/klokkos/klee/wiki).

```
export PROJECT_DIR="$HOME/projects/xstack"
export LIBCXX_DIR="$PROJECT_DIR/libcxx"
```

The kleekos branch `build.sh` is modified to not automatically install required packages, but report the packages it would have installed.  On a personal machine, auto install may have unintended effects.

Run the following to build CXX libs.  Manually install missing packages.

```
LLVM_VERSION=13 BASE=$LIBCXX_DIR ENABLE_OPTIMIZED=1 DISABLE_ASSERTIONS=1 ENABLE_DEBUG=0 REQUIRES_RTTI=1 klee/scripts/build/build.sh libcxx
```

```
mkdir build-release && cd build-release
cmake .. -G Ninja \
 -DCMAKE_BUILD_TYPE=Release \
 -DCMAKE_INSTALL_PREFIX=/usr/local/stow/klee \
 -DENABLE_KLEE_UCLIBC=ON \
 -DENABLE_POSIX_RUNTIME=ON \
 -DKLEE_UCLIBC_PATH=$PROJECT_DIR/klee-uclibc \
 -DENABLE_KLEE_LIBCXX=ON \
 -DKLEE_LIBCXX_DIR=$LIBCXX_DIR/libc++-install-130/ \
 -DKLEE_LIBCXX_INCLUDE_DIR=$LIBCXX_DIR/libc++-install-130/include/c++/v1/ \
 -DENABLE_KLEE_EH_CXX=ON \
 -DKLEE_LIBCXXABI_SRC_DIR=$LIBCXX_DIR/llvm-130/libcxxabi/ \
 -DENABLE_UNIT_TESTS=OFF \
 -DENABLE_SYSTEM_TESTS=OFF
```
