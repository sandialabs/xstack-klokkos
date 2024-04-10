cmake_minimum_required(VERSION 3.17)
project(RaceConditionExample)

# Put the location of Kokkos Model (Change to your own directory)
set(KokkosModelPATH "/home-emu/smukher/Kokkos-work/KLOKKOS/Kokkos-Model")
set(KLEEPATH "/home-emu/smukher/Kokkos-work/klee")
set(CMAKE_PREFIX_PATH /home-emu/smukher/Kokkos-work/build-klokkos-model)
set(CMAKE_VERBOSE_MAKEFILE ON)
set(CMAKE_C_COMPILER /opt/spack/c7.7/compilers-20201207/spack/opt/spack/linux-centos7-x86_64/gcc-5.5.0/llvm-9.0.1-isbmi7byzku7urwwdcp3dlvgkn4s2ras/bin/clang)
set(CMAKE_CXX_COMPILER /opt/spack/c7.7/compilers-20201207/spack/opt/spack/linux-centos7-x86_64/gcc-5.5.0/llvm-9.0.1-isbmi7byzku7urwwdcp3dlvgkn4s2ras/bin/clang++)
set(CMAKE_CXX_FLAGS "-emit-llvm -c -g -O0 -Xclang -disable-O0-optnone -std=gnu++14")
set(CMAKE_CXX_STANDARD 14)

#include_directories( ../include
#   ${SOME_OTHER_PATH}/include
#)
include_directories(${KLEEPATH}/include
   ${KokkosModelPATH}
)
add_executable(RaceConditionEaxmple1_Lambda RaceCondition_parallel_for_lambda.cpp)

target_link_libraries(RaceConditionExample1_Lambda PUBLIC KokkosModel)
