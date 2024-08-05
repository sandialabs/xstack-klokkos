

#include <cstdio>
#include <Kokkos_Core.hpp>
//
// This is using lambda
//
int main( int argc, char *argv[] )
{
    Kokkos::initialize(argc,argv);
    {
        const int n = 1024;
        double sum = 0;
        Kokkos::View<double *> A("A",n);  // Allocated on the default device.
        Kokkos::View<double *>::HostMirror A_host = Kokkos::create_mirror_view(A);  // If the default is host, hostA is going to be a simple soft copy

        //
        // hostA can be accessed outside the default execution space.  We can explicitly say host execution space
        //
        for ( int i = 0; i < n; ++i )
        {
            A_host (i) = (double )i;
        }

        // This is a blocking call
        // If the mirror view is (A_host) already referencing A in the same memory space, no operation happens.
        Kokkos::deep_copy(A,A_host);

        // Choosing the default execution space. This should work for any platforms.
        Kokkos::parallel_reduce( n, KOKKOS_LAMBDA(const int i, double & lsum ) {
            lsum += A(i) * A(i); // Computation happens in the default device
        }, sum);

        // Compare to a sequential loop on CPU.
        double seqSum = 0;
        for (int i = 0; i < n; ++i) {
            seqSum += (double )i * (double) i;
        }
        
        printf(
                "Sum of squares of integers from 0 to %i, "
                "computed sequentially, is %e\n",
                n - 1, seqSum);

        if( std::abs(sum - seqSum )/std::abs(sum) < 1e-8 ) {
            printf("SUCCESS %e %e\n",sum,seqSum);
        } else {
            printf("Fail %e %e\n",sum,seqSum);
        }
    }

    Kokkos::finalize();
    return 0;
}
