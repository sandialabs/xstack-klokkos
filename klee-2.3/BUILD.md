Build instructions
=============================

See KLEE instructions for building dependancies.

export PROJECT_ROOT=$HOME/projects/foss
export UCLIBC_DIR=$PROJECT_ROOT/klee-uclibc
export LIBCXX_DIR=$PROJECT_ROOT/klee-libcxx

```
cmake .. -G Ninja \
  -DENABLE_UNIT_TESTS=OFF \
  -DENABLE_SYSTEM_TESTS=OFF \
  -DENABLE_SOLVER_STP=ON \
  -DENABLE_POSIX_RUNTIME=ON \
  -DENABLE_KLEE_UCLIBC=ON \
  -DKLEE_UCLIBC_PATH=$UCLIBC_DIR \
  -DENABLE_SOLVER_Z3=ON \
  -DENABLE_KLEE_LIBCXX=ON \
  -DKLEE_LIBCXX_DIR=$LIBCXX_DIR/libc++-install-130/ \
  -DKLEE_LIBCXX_INCLUDE_DIR=$LIBCXX_DIR/libc++-install-130/include/c++/v1/ \
  -DENABLE_KLEE_EH_CXX=ON \
  -DKLEE_LIBCXXABI_SRC_DIR=$LIBCXX_DIR/llvm-130/libcxxabi/ \
  -DCMAKE_INSTALL_PREFIX=/usr/local/stow/klee \
  -DCMAKE_BUILD_TYPE=Debug \
```

Hints for building libcxx - Warning! the automated scripts try to install packages!!!
Disable by editing `common-functions` to stub out `with_sudo`.

