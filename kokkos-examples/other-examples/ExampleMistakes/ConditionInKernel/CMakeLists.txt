cmake_minimum_required(VERSION 3.17)
project(Fuzzing)

set(CMAKE_CXX_STANDARD 14)

file(GLOB SOURCES "*.cpp")

#add_executable(MatrixComputationSerial MatrixComputationSerial.cpp)
#add_executable(MatrixComputationCuda MatrixComputationCuda.cpp)
add_executable(Driver ${SOURCES})

find_package(Kokkos REQUIRED)
find_package(OpenMP)

#target_link_libraries(MatrixComputationSerial PUBLIC Kokkos::kokkos)
#target_link_libraries(MatrixComputationCuda PUBLIC Kokkos::kokkos)
target_link_libraries(Driver PUBLIC Kokkos::kokkos)
