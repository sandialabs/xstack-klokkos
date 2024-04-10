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
    for ( int i = 0; i < n; ++i )
    {
        printf("Hello Wolrd %d\n",i);
    };
    return 0;
}