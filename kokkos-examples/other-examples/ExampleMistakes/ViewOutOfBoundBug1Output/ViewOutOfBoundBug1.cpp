#include <cstdio>
#include <cmath>
#include <Kokkos_Core.hpp>
//
// This Program includes a mistake of Kokkos::View out-of-bound access
//

int main( int argc, char *argv[] )
{
    Kokkos::initialize(argc,argv);
    {
        int view_size = 100;
        if (argc == 2) {
            view_size = atoi (argv[1]);
        }
        //
        // Default Execution Space is determined by the library-build time.
        // If the default is NVIDIA/AMD GPUs, you will get runtime error
        Kokkos::View<double *>  A("A",view_size); // Allocated in the Default Memory Space
        auto A_M = Kokkos::create_mirror_view(A); // Allocated in the Default Memory Space
        Kokkos::deep_copy( A, 1.0 ); // Assign 1s to all entries of A.

#ifdef WITH_BUG
        // Using a simple parallel_for
        Kokkos::parallel_for(200, KOKKOS_LAMBDA(const int i)
        {
            A( i ) =  static_cast<double>(i);  // Runtime error, out of bounds. The error could manifest somewhere else.
        });
#elif WITH_FIX_1
        // Put the size of A explicitly
        // Assuming the user wants to update all the entries of A
        Kokkos::parallel_for(100, KOKKOS_LAMBDA(const int i)
        {
            A( i ) =  static_cast<double>(i);  // Works as A.extent(0) is 100.
        });
#elif WITH_FIX_2

        // Extent return the size for the given dimension.
        Kokkos::parallel_for(A.extent(0), KOKKOS_LAMBDA(const int i)
        {
            A( i ) =  static_cast<double>(i);  // Works as A.extent(0) is 100.
        });
#else
        // It's identical with FIX_2, but I explicitly create RangePolicy with the default execution space
        Kokkos::parallel_for(Kokkos::RangePolicy<>(0, A.extent(0)), KOKKOS_LAMBDA(const int i)
        {
            A( i ) =  static_cast<double>(i);  // Works as A.extent(0) is 100.
        });
#endif
        Kokkos::deep_copy(A_M, A );
        for( int i = 0; i < A_M.extent(0); ++i ) 
        {
            std::cout << "A ( " << i << " ) : " << A_M(i) << std::endl;
        }
    }
    Kokkos::finalize();
    return 0;
}
