#include <Kokkos_Core.hpp>

#define N 256
#define M 128

int main(int argc, char * argv[]) {
  Kokkos::initialize(argc,argv);
  {
    Kokkos::View<int *> view1("1", N);
#ifdef WITH_BUG
    Kokkos::View<int *> view2("2", M);
#else
    Kokkos::View<int *> view2("2", N);
#endif
    Kokkos::parallel_for(N, KOKKOS_LAMBDA(const size_t index) {
        view1(index) = index;
    });

    Kokkos::deep_copy(view1, view2);
  }
  Kokkos::finalize();
  return 0;
}
