#include <cstdio>
#include <cstdlib>
#include <Kokkos_Core.hpp>
//
// This is using lambda
//
int main( int argc, char *argv[] )
{
    int n;
    if (argc == 2)
        n = atoi (argv[1]);
    else
        n = 10;

    Kokkos::initialize(argc,argv);
    {
        // Use the default policy
        Kokkos::parallel_for( n, KOKKOS_LAMBDA(const int i)
        {
            printf("Hello Wolrd %d\n",i);
        });
    }
    Kokkos::finalize();
    return 0;
}
