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
            Kokkos::DualView<double *> B("A", N); // Allocated in the Default Memory Space

   

            Kokkos::parallel_for (N , KOKKOS_LAMBDA ( const size_t index )
            {
                B.d_view(index) = index; 
            });

//#ifdef WITH_BUG
#if 0
            Kokkos::parallel_for (Kokkos::RangePolicy<>(1,N) , KOKKOS_LAMBDA ( const size_t index )
            {
                B.d_view(index) = B.d_view(index-1); 
                std::cout << "B( " << index << " ) =  " <<  B.d_view(index) << std::endl; 
            });
#else
            Kokkos::parallel_for(Kokkos::RangePolicy<>(1,N), KOKKOS_LAMBDA(const size_t index) {
                A.d_view(index) = B.d_view(index-1); 
            });
            Kokkos::parallel_for(N, KOKKOS_LAMBDA(const size_t index) {
                B.d_view(index) = A.d_view(index); 
            });
#endif
          
            Kokkos::deep_copy(B.h_view, B.d_view);
            // Showing the value of B
            for ( int i = 0 ; i < N; ++i ) 
            {
                std::cout << "B( " << i << " ) =  " <<  B.h_view(i) << std::endl; 
            }
        }
    }

    Kokkos::finalize();
    return 0;
}
