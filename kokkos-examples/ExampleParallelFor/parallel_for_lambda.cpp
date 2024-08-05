#include <cstdio>
#include <vector>
#include <Kokkos_Core.hpp>
//
// This is using lambda
//
int main( int argc, char *argv[] )
{
    Kokkos::initialize(argc,argv);
    {
        const int n = 10;


        Kokkos::View<double *> A("A",n); // Kokkos::View in the default memory space
        Kokkos::View<double *>::HostMirror A_host = Kokkos::create_mirror_view(A);
        //
        // Create Execution Policy on Host
        //
        Kokkos::parallel_for( Kokkos::RangePolicy<Kokkos::Serial>(0,n), KOKKOS_LAMBDA ( const int i )
        {
           A_host(i) = (double )(i+1);
        });

        Kokkos::deep_copy(A,A_host);

        // Choosing the default execution space. This should work for any platforms.
        Kokkos::parallel_for( Kokkos::RangePolicy<Kokkos::DefaultExecutionSpace>( 0,n), KOKKOS_LAMBDA ( const int i )
        {
            A(i) *= 2.0;  // Scalar-Vector Multiplication
        });

        Kokkos::deep_copy(A_host,A); // COpy the data back to CPU

        // Compare to a sequential loop on CPU.
        std::vector<double>  A_verify(10);
        for (int i = 0; i < n; ++i) {
            A_verify[i] = (double)(i+1);
        }
        for (int i = 0; i < n; ++i) {
           A_verify[i] *= 2.0;
        }

        double sum = 0;
        for ( int i = 0; i < n; ++i )
        {
            A_verify[i] -= A_host(i);  // if "A" is used for the computation. Throw error
            sum += A_verify[i]/A_host(i);
        }

        if( sum < 1e-8 ) {
            printf("SUCCESS\n");
        } else {
            printf("Fail %e\n",sum);
        }
    }

    Kokkos::finalize();
    return 0;
}
