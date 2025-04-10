#include <cstdio>
#include <cstdlib>
#include <Kokkos_Core.hpp>
//
// Bug: Incorrect computation because the if statement at the end of the code expects A has not been altered since the initialization. 
//

int main( int argc, char *argv[] )
{
    Kokkos::initialize(argc,argv);
    {
        int samples;
        if (argc != 2) {
            samples = 100;
        } else {
            samples = std::stoi(argv[1]);
        }

        Kokkos::View<double *> A("A",samples);

#ifdef WITH_BUG
        Kokkos::View<double *> B = A; // Soft copy. B has been aliased by A.
#else
        Kokkos::View<double *> B ("B",samples); // B is an independent container.
#endif
        Kokkos::deep_copy(A,1.0); // Initializing A

        Kokkos::deep_copy(B,A); // The entries in A is copied to B

        Kokkos::parallel_for(B.extent(0), KOKKOS_LAMBDA(const int i)
        {
            B( i ) =  static_cast<double>(i);  // We are modifying B assuming A and B are independent.
        });

        double mySum = 0;
        Kokkos::parallel_reduce(A.extent(0), KOKKOS_LAMBDA(const int i, double &local_sum )
        {
            local_sum += A(i); // every value of A is no longer 1.0 as A has been overwritten by the previous parallel_for
        },mySum);

        double solution = static_cast<double>(samples-1) * samples * 0.5;

        if( mySum == static_cast<double>(samples) )
        {
            std::cout << "A is not changed, Life is Good " << mySum << " . Expected Value:" <<static_cast<double>(samples) << std::endl;
        } else {
            std::cout << "A has been altered. Why? " << mySum << " . Expected Value:" <<static_cast<double>(samples) << std::endl;
        }
    }

    Kokkos::finalize();
    return 0;
}