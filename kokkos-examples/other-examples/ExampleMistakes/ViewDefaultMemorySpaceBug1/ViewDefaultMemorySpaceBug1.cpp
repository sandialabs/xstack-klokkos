#include <cstdio>
#include <Kokkos_Core.hpp>
//
// This Program includes a mistake of using Default Memory Space.  The error happens when using AMD/NVIDIA GPUs
//

int main( int argc, char *argv[] )
{
    Kokkos::initialize(argc,argv);
    {
        //
        // Default Execution Space is determined by the library-build time.
        // If the default is NVIDIA/AMD GPUs, you will get runtime erorr
        Kokkos::View<double *, Kokkos::HostSpace> A("A",100); // Allocated in the HostSpace
        Kokkos::View<double *>  B("B",100); // Allocated in the Default Memory Space

        Kokkos::deep_copy( A, 1.0 ); // Assign 1s to all entries of A.
        Kokkos::deep_copy( B, 1.0 ); // Assign 1s to all entries of B.


#ifdef WITH_BUG
        for (int i = 0; i < B.extent(0); ++i  )
        {
            B( i ) =  static_cast<double>(i);  // Runtime error if the default mem-space is CUDA or ROCm
        }
#elsif WITH_FIX_1
        for (int i = 0; i < A.extent(0); ++i  )
        {
            A( i ) = static_cast<double>(i);  // Host Memory Space can be accessed by a regular host program
        }
#else
        // Use Parallel_for for the execution space to make sure B (default memory space) is executed
        // in the right space.
        Kokkos::parallel_for("Fix2",100,KOKKOS_LAMBDA( const int &i ) 
        {
            B( i ) = static_cast<double>(i);  
        });
#endif

    }

    Kokkos::finalize();
    return 0;
}
