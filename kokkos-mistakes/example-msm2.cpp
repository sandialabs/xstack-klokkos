#include <iostream>
#include <Kokkos_Core.hpp>

#define N 32

int main(int argc, char * argv[]) {

  int final_answer;

  Kokkos::initialize(argc,argv);
  {
    Kokkos::View<int *> view("V", N);
    Kokkos::parallel_for(N, KOKKOS_LAMBDA(const size_t index) {
        view(index) = index;
    });

#ifdef WITH_BUG
    final_answer = view(0);
#else
    Kokkos::View<int *>::HostMirror host = Kokkos::create_mirror_view(view);
    Kokkos::deep_copy(host, view);
    final_answer = host(0);
#endif
  }
  Kokkos::finalize();
  return 0;
}
