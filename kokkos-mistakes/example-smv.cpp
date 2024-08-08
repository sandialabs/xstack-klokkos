#include <iostream>
#include <Kokkos_Core.hpp>

#define N 32

int main(int argc, char * argv[]) {

  int final_answer;

  Kokkos::initialize(argc,argv);
  // d_view -> view in default address space
  // h_view -> view in host address space
  Kokkos::View<int *> d_view("V", N);
  Kokkos::View<int *>::HostMirror h_view = Kokkos::create_mirror_view(d_view);

  // initialize the host view and copy to the default address space
  for (int idx = 0; idx < N; ++idx) {
    h_view(idx) = idx;
  }
  Kokkos::deep_copy(d_view, h_view);

  // perform computation in the default execution space
  Kokkos::parallel_for(N, KOKKOS_LAMBDA(const size_t index) {
      d_view(index) = 2 * d_view(index);
  });

#ifdef WITH_BUG
  // without the deep_copy, h_view will be stale.

#else
  // copy default view back to host
  Kokkos::deep_copy(h_view, d_view);
#endif

  // access a value in host view
  final_answer = h_view(1);

  Kokkos::finalize();
  return 0;
}
