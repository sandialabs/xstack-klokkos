cmake_minimum_required(VERSION 3.16)

project(CanonicalExamples)
set(CMAKE_CXX_STANDARD 14)

find_package(Kokkos)

add_executable(example-dcm-buggy example-dcm.cpp)
add_executable(example-dcm-nobug example-dcm.cpp)
target_compile_definitions(example-dcm-buggy-buggy PRIVATE WITH_BUG=1)
target_link_libraries(example-dcm-buggy PUBLIC Kokkos::kokkos)
target_link_libraries(example-dcm-nobug PUBLIC Kokkos::kokkos)

add_executable(example-io-buggy example-io.cpp)
add_executable(example-io-nobug example-io.cpp)
target_compile_definitions(example-io-buggy PRIVATE WITH_BUG=1)
target_link_libraries(example-io-buggy PUBLIC Kokkos::kokkos)
target_link_libraries(example-io-nobug PUBLIC Kokkos::kokkos)

add_executable(example-msm1-buggy example-msm1.cpp)
add_executable(example-msm1-nobug example-msm1.cpp)
target_compile_definitions(example-msm1-buggy PRIVATE WITH_BUG=1)
target_link_libraries(example-msm1-buggy PUBLIC Kokkos::kokkos)
target_link_libraries(example-msm1-nobug PUBLIC Kokkos::kokkos)

add_executable(example-msm2-buggy example-msm2.cpp)
add_executable(example-msm2-nobug example-msm2.cpp)
target_compile_definitions(example-msm2-buggy PRIVATE WITH_BUG=1)
target_link_libraries(example-msm2-buggy PUBLIC Kokkos::kokkos)
target_link_libraries(example-msm2-nobug PUBLIC Kokkos::kokkos)

add_executable(example-smv-buggy example-smv.cpp)
add_executable(example-smv-nobug example-smv.cpp)
target_compile_definitions(example-smv-buggy PRIVATE WITH_BUG=1)
target_link_libraries(example-smv-buggy PUBLIC Kokkos::kokkos)
target_link_libraries(example-smv-nobug PUBLIC Kokkos::kokkos)

add_executable(example-voob1-buggy example-voob1.cpp)
add_executable(example-voob1-nobug example-voob1.cpp)
target_compile_definitions(example-voob1-buggy PRIVATE WITH_BUG=1)
target_link_libraries(example-voob1-buggy PUBLIC Kokkos::kokkos)
target_link_libraries(example-voob1-nobug PUBLIC Kokkos::kokkos)

add_executable(example-voob2-buggy example-voob2.cpp)
add_executable(example-voob2-nobug example-voob2.cpp)
target_compile_definitions(example-voob2-buggy PRIVATE WITH_BUG=1)
target_link_libraries(example-voob2-buggy PUBLIC Kokkos::kokkos)
target_link_libraries(example-voob2-nobug PUBLIC Kokkos::kokkos)
