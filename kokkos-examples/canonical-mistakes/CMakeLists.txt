cmake_minimum_required(VERSION 3.16)

project(CanonicalExamples)
set(CMAKE_CXX_STANDARD 14)

find_package(Kokkos)

add_executable(example1-buggy example1.cpp)
add_executable(example1-nobug example1.cpp)
target_compile_definitions(example1-buggy PRIVATE WITH_BUG=1)
target_link_libraries(example1-buggy PUBLIC Kokkos::kokkos)
target_link_libraries(example1-nobug PUBLIC Kokkos::kokkos)

add_executable(example2-buggy example2.cpp)
add_executable(example2-nobug example2.cpp)
target_compile_definitions(example2-buggy PRIVATE WITH_BUG=1)
target_link_libraries(example2-buggy PUBLIC Kokkos::kokkos)
target_link_libraries(example2-nobug PUBLIC Kokkos::kokkos)

add_executable(example3-buggy example3.cpp)
add_executable(example3-nobug example3.cpp)
target_compile_definitions(example3-buggy PRIVATE WITH_BUG=1)
target_link_libraries(example3-buggy PUBLIC Kokkos::kokkos)
target_link_libraries(example3-nobug PUBLIC Kokkos::kokkos)

#add_executable(example4-buggy example4.cpp)
#add_executable(example4-nobug example4.cpp)
#target_compile_definitions(example4-buggy PRIVATE WITH_BUG=1)
#target_link_libraries(example4-buggy PUBLIC Kokkos::kokkos)
#target_link_libraries(example4-nobug PUBLIC Kokkos::kokkos)

add_executable(example5-buggy example5.cpp)
add_executable(example5-nobug example5.cpp)
target_compile_definitions(example5-buggy PRIVATE WITH_BUG=1)
target_link_libraries(example5-buggy PUBLIC Kokkos::kokkos)
target_link_libraries(example5-nobug PUBLIC Kokkos::kokkos)
