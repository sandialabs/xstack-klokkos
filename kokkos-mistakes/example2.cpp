#include <iostream>
#include <Kokkos_Core.hpp>

#define DEFAULT_N 256

int main(int argc, char *argv[]) {

  // Initialize Kokkos
  Kokkos::initialize(argc, argv);
  {
    int N = DEFAULT_N;
    int final_answer;

    // allocate view on default device and initialize it
    Kokkos::View<int *> dA("A", N); // Allocated in the Default Memory Space
    Kokkos::parallel_for(N , KOKKOS_LAMBDA(const size_t index) {
      dA(index) = index;
    });

#ifdef WITH_BUG
    Kokkos::parallel_for(Kokkos::RangePolicy<>(1, N), KOKKOS_LAMBDA(const size_t index) {
      dA(index) = dA(index-1);
    });
#else
    Kokkos::View<int *> dCopy("Copy", N); // Allocated in the Default Memory Space
    Kokkos::parallel_for(Kokkos::RangePolicy<>(1,N), KOKKOS_LAMBDA(const size_t index) {
      dCopy(index) = dA(index-1);
    });
    Kokkos::parallel_for(N, KOKKOS_LAMBDA(const size_t index) {
      dA(index) = dCopy(index);
    });
#endif
    auto hA = Kokkos::create_mirror_view(dA);
    Kokkos::deep_copy(hA, dA);
    final_answer = hA(0);
  }
  Kokkos::finalize();
  return 0;
}
