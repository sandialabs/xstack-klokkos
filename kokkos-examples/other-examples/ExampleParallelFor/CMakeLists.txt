cmake_minimum_required(VERSION 3.17)
project(ParallelForExample)

# Put the location of Kokkos (Change to your own directory)
set(CMAKE_PREFIX_PATH /Users/knteran/Kokkos)

set(CMAKE_CXX_STANDARD 14)

#add_executable(ParallelForExample1 parallel_for_functor1.cpp)
add_executable(ParallelForExample1_Lambda parallel_for_lambda.cpp)
add_executable(ParallelForExample1_NoKokkos parallel_for_nokokkos.cpp)

#add_executable(ReduceMistake1_NoKokkos main_no_kokkos.cpp)
find_package(Kokkos)
find_package(OpenMP)
if (OPENMP_FOUND)
    set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${OpenMP_C_FLAGS}")
    set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
    set (CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${OpenMP_EXE_LINKER_FLAGS}")
endif()
target_link_libraries(ParallelForExample1_Lambda PUBLIC Kokkos::kokkos)
