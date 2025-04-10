#include <iostream>
#include <Kokkos_Core.hpp>

#define N 32

int main(int argc, char * argv[]) {
  Kokkos::initialize(argc,argv);
  {
#ifdef WITH_BUG
    Kokkos::View<int *, Kokkos::HostSpace> view ("V", N);
#else
    Kokkos::View<int *> view("V", N);
#endif

    Kokkos::parallel_for(N, KOKKOS_LAMBDA(const size_t index) {
        view(index) = index;
    });
  }
  Kokkos::finalize();
  return 0;
}
