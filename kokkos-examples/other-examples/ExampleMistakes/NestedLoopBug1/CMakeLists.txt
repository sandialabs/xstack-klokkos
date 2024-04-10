cmake_minimum_required(VERSION 3.17)
project(ReduceExample)

# Put the location of Kokkos (Change to your own directory)
#set(CMAKE_PREFIX_PATH /Users/knteran/Kokkos)
set(CMAKE_CXX_STANDARD 14)

### UNCOMMENT THIS LINE TO ENABLE THE BUGS IN THE PROGRAMS
#set(CMAKE_CXX_FLAGS "-DWITH_BUG")
###

add_executable(NestedLoopBug1 NestedLoopBug1.cpp)
find_package(Kokkos)
find_package(OpenMP)
   # if (OPENMP_FOUND)
   #     set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${OpenMP_C_FLAGS}")
   #     set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
   #     set (CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${OpenMP_EXE_LINKER_FLAGS}")
   # endif()
target_link_libraries(NestedLoopBug1 PUBLIC Kokkos::kokkos)
