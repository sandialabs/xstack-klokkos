cmake_minimum_required(VERSION 3.19)
project(KokkosModel)
#
# Use Clang Compiler with the one used for KLEE.
#
# Use export macro to set CC and CXX
#
set(CMAKE_VERBOSE_MAKEFILE ON)
set(CMAKE_C_COMPILER /opt/spack/c7.7/compilers-20201207/spack/opt/spack/linux-centos7-x86_64/gcc-5.5.0/llvm-9.0.1-isbmi7byzku7urwwdcp3dlvgkn4s2ras/bin/clang)
set(CMAKE_CXX_COMPILER /opt/spack/c7.7/compilers-20201207/spack/opt/spack/linux-centos7-x86_64/gcc-5.5.0/llvm-9.0.1-isbmi7byzku7urwwdcp3dlvgkn4s2ras/bin/clang++)
set(CMAKE_CXX_FLAGS "-emit-llvm -c -g -O0 -Xclang -disable-O0-optnone -std=gnu++14")
set(CMAKE_CXX_STANDARD 14)
#
# Import the custom functions
#
list(APPEND CMAKE_MODULE_PATH "/home-emu/smukher/Kokkos-work/llvm-ir-cmake-utils/cmake")
message(STATUS ${CMAKE_MODULE_PATH})
#

# general defs

set(SOURCES  Kokkos_Model.cpp)
# directory level

# target level
add_library(KokkosModel ${SOURCES})
set_target_properties(KokkosModel PROPERTIES LINKER_LANGUAGE CXX)
if(CMAKE_CXX_COMPILER_VERSION VERSION_GREATER_EQUAL "5.0.0" OR
    CMAKE_CXX_COMPILER_VERSION VERSION_EQUAL "5.0.0")
  target_compile_options(KokkosModel PUBLIC -Xclang -disable-O0-optnone)
endif()
#


