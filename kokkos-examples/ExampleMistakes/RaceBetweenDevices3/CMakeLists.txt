cmake_minimum_required(VERSION 3.17)
project(ReduceExample) 

# Put the location of Kokkos (Change to your own directory)
#set(CMAKE_PREFIX_PATH /Users/knteran/Kokkos)
set(CMAKE_CXX_STANDARD 14) # Note: latest kokkos 4.0 requires cmake version 17

### UNCOMMENT THIS LINE TO ENABLE THE BUGS IN THE PROGRAMS
#set(CMAKE_CXX_FLAGS "-DWITH_BUG")
###

add_executable(RaceBetweenDevices3 RaceBetweenDevices3.cpp)

add_executable(RaceBetweenDevices3-penmp RaceBetweenDevices3-openmp.cpp)

find_package(Kokkos)
find_package(OpenMP)
  if (OPENMP_FOUND)
      set (CMAKE_C_FLAGS "${CMAKE_C_FLAGS} ${OpenMP_C_FLAGS}")
      set (CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
       set (CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${OpenMP_EXE_LINKER_FLAGS}")
  endif()
target_link_libraries(RaceBetweenDevices3 PUBLIC Kokkos::kokkos)

target_link_libraries(RaceBetweenDevices3-openmp PUBLIC OpenMP)

# using klokkos model - no Kokkos
target_link_libraries(RaceBetweenDevices
3-klokkos PUBLIC)

