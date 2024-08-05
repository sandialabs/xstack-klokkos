#include <cstdio>
#include <cstdlib>
#include <Kokkos_Core.hpp>
#include <Kokkos_DualView.hpp>
//
// The bug only shows up with a certain parallel architecture
// Bug: Incorrect computation. Real code may find the correctness issues in completely different place
//

int main( int argc, char *argv[] )
{

    Kokkos::initialize(argc,argv);
    {

        if (argc != 2) {
            std::cout << "Please pass one integers on the command line" << std::endl;
        } else {
            // Initialize Kokkos
            int N = std::stoi(argv[1]);

            //
            // Default Execution Space is determined by the library-build time.
            // If the default is NVIDIA/AMD GPUs, you will get runtime eror
            Kokkos::DualView<double *> A("A", N); // Allocated in the Default Memory Space

            Kokkos::deep_copy(A.h_view, 0.0);
            Kokkos::deep_copy(A.d_view, A.h_view);

#ifdef WITH_BUG
            Kokkos::parallel_for (N , KOKKOS_LAMBDA ( const size_t index )
            {
                A.d_view(index%2) = index; // The value of A(index%2) is undeterministic
            });
#else
            Kokkos::parallel_for(N, KOKKOS_LAMBDA(const size_t index) {
                A.d_view(index) = index;
            });
#endif

            Kokkos::deep_copy(A.h_view, A.d_view);
        }
    }

    Kokkos::finalize();
    return 0;
}
