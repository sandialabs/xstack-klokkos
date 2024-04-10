#include <cstdio>
#include <vector>

//
// This is using lambda
//
int main( int argc, char *argv[] )
{
    const int n = 10;

    std::vector<double> A(10);
    for (int i = 0; i < n; ++i ) {
        A[i] = (double )(i+1);
    }
    for (int i = 0; i < n; ++i ) {
        A[i] *= 2.0;
    }

    // Compare to a sequential loop on CPU.
    std::vector<double>  A_verify(10);
    for (int i = 0; i < n; ++i) {
        A_verify[i] = (double) (i+1);
    }
    for (int i = 0; i < n; ++i) {
        A_verify[i] *= 2.0;
    }

    double sum = 0;
    for ( int i = 0; i < n; ++i )
    {
        printf("%e %e\n",A_verify[i],A[i]);
        A_verify[i] -= A[i];
        sum += A_verify[i]/A[i];
    }

    if( sum < 1e-8 ) {
        printf("SUCCESS\n");
    } else {
        printf("Fail %e\n",sum);
    }
    return 0;
}
