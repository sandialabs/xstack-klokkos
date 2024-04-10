cmake_minimum_required(VERSION 3.16)

project(CanonicalExamples)
set(CMAKE_CXX_STANDARD 14)

find_package(Kokkos)

add_executable(example1 example1.cpp)
add_executable(example2 example2.cpp)
add_executable(example3 example3.cpp)
add_executable(example4 example4.cpp)

target_link_libraries(example1 PUBLIC Kokkos::kokkos)
target_link_libraries(example2 PUBLIC Kokkos::kokkos)
target_link_libraries(example3 PUBLIC Kokkos::kokkos)
target_link_libraries(example4 PUBLIC Kokkos::kokkos)
