#include <iostream>
#include <Kokkos_Core.hpp>

#define N 128
#define M 256

int main(int argc, char * argv[]) {
  Kokkos::initialize(argc,argv);
  {
    Kokkos::View<int *> view("v", N);
#ifdef WITH_BUG
    unsigned tasks = M;
#else
    unsigned tasks = N;
#endif
    Kokkos::parallel_for(tasks, KOKKOS_LAMBDA(const size_t index) {
        view(index) = index;
    });
  }
  Kokkos::finalize();
  return 0;
}
