#include <cstdio>
#include <Kokkos_Core.hpp>
//
// This is using lambda
//
int main( int argc, char *argv[] )
{
    Kokkos::initialize(argc,argv);
    {
        const int n = 10;
        int sum = 0;

        // There is a bug.  int &lsum is correct.
        Kokkos::parallel_reduce(
                n, KOKKOS_LAMBDA(const int i, int  lsum) {
                    lsum += i * i;
        }, sum);


        // Compare to a sequential loop on CPU.
        int seqSum = 0;
        for (int i = 0; i < n; ++i) {
            seqSum += i * i;
        }
        printf(
                "Sum of squares of integers from 0 to %i, "
                "computed sequentially, is %i\n",
                n - 1, seqSum);
        if( sum == seqSum ) {
            printf("SUCCESS\n");
        } else {
            printf("Fail %d %d\n",sum,seqSum);
        }
    }

    Kokkos::finalize();
    return 0;
}
