#include <iostream>
#include <Kokkos_Core.hpp>

// Define the stencil computation function
void stencil_3d_kokkos(const Kokkos::View<double***>& input, Kokkos::View<double***>& output, int nx, int ny, int nz, int bx, int by, int bz) {
  typedef Kokkos::MDRangePolicy<Kokkos::Rank<3>> policy_t;

  // Define the blocked stencil kernel
  Kokkos::parallel_for("stencil_3d", policy_t({1, 1, 1}, {nx-1, ny-1, nz-1}, {bx, by, bz}), KOKKOS_LAMBDA(int i, int j, int k) {
    output(i, j, k) = input(i, j, k) * (-6.0) +
                      input(i - 1, j, k) +
                      input(i + 1, j, k) +
                      input(i, j - 1, k) +
                      input(i, j + 1, k) +
                      input(i, j, k - 1) +
                      input(i, j, k + 1);
  });
}

int main(int argc, char* argv[]) {
  Kokkos::initialize(argc, argv);
  {
    int nx = 128, ny = 128, nz = 128;
    int N = 10; // Number of iterations

    // Define block sizes
    int bx = 8, by = 8, bz = 8;

    // Define the policy_t inside main()
    typedef Kokkos::MDRangePolicy<Kokkos::Rank<3>> policy_t;

    // Allocate input and output 3D arrays
    Kokkos::View<double***> input("input", nx, ny, nz);
    Kokkos::View<double***> output("output", nx, ny, nz);

    // Initialize input data
    Kokkos::parallel_for("initialize", policy_t({0, 0, 0}, {nx, ny, nz}), KOKKOS_LAMBDA(int i, int j, int k) {
      input(i, j, k) = 1.0 * i * j * k / (nx * ny * nz);
    });
    Kokkos::deep_copy(output, input);

    // Run stencil computation N times with blocking
    for (int iter = 0; iter < N; ++iter) {
      stencil_3d_kokkos(input, output, nx, ny, nz, bx, by, bz);
      // Swap input and output for the next iteration
#ifdef _WITH_BUG    
      auto tmp = output;
      output = input;
      input = tmp;
#else

      // Kokkos::deep_copy(input, output);
      Kokkos::fence();
      auto tmp = output;
      output = input;
      input = tmp;
#endif
    }
  }
  Kokkos::finalize();
  return 0;
}
