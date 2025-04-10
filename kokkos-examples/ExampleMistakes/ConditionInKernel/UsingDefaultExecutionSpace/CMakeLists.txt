cmake_minimum_required(VERSION 3.17)
project(ConditionInKernel)

set(CMAKE_CXX_STANDARD 14)

file(GLOB SOURCES "*.cpp")

# add_executable(MatrixComputation MatrixComputation.cpp)
add_executable(simple simple.cpp)
add_executable(simple-fixed simple-fixed.cpp)
add_executable(simple-fixed++ simple-fixed++.cpp)

find_package(Kokkos REQUIRED)
find_package(OpenMP)

# target_link_libraries(MatrixComputation PUBLIC Kokkos::kokkos)
target_link_libraries(simple PUBLIC Kokkos::kokkos)
target_link_libraries(simple-fixed PUBLIC Kokkos::kokkos)
target_link_libraries(simple-fixed++ PUBLIC Kokkos::kokkos)
