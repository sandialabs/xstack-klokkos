#include <cstdio>
#include <Kokkos_Core.hpp>
//
// This Program includes a mistake of Kokkos::deep_copy where the size does not match 
// between src and dst Kokkos::Views.
//
int main( int argc, char *argv[] )
{
    Kokkos::initialize(argc,argv);
    {
        Kokkos::View<double *>  A("A",100); // Allocated in the Default Memory Space
        Kokkos::View<double *>  B("B",10); // Allocated in the Default Memory Space

        Kokkos::deep_copy( A, 1.0 ); // Assign 1s to all entries of A.
#ifdef WITH_BUG
        Kokkos::deep_copy( B, A ); // It triggers a runtime error as the size of B and A does not match.
#elif WITH_BUG_2
        // It triggers a runtime error because subview is making an out-of-band access to A
        Kokkos::deep_copy( B, Kokkos::subview( A, std::pair<int,int>(100,110) ); 
#elif WITH_FIX_1
        // This fix is intended to provide an access to the first 10 entries of A for the source.
        Kokkos::deep_copy( B, Kokkos::subview( A, std::pair<int,int>(0,10) ) );
#elif WITH_FIX_2 
        // This fix is intended to provide an access from 20th to 30th entries of A for the source. 
        Kokkos::deep_copy( B, Kokkos::subview( A, std::pair<int,int>(20,30) ) );                                                                                                                                                 
#else
        // This fix is resizing B so that B can take all the entries from A
        Kokkos::resize(B,100);
        Kokkos::deep_copy(B,A);
#endif

    }

    Kokkos::finalize();
    return 0;
}
