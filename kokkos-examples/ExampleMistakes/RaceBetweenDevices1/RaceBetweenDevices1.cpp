#include <cstdio>
#include <cstdlib>
#include <Kokkos_Core.hpp>
//
// The bug only shows up with a certain parallel architecture
// Bug: Incorrect computation. Real code may find the correctness issues in completely different place
//
#define MYEXEC_SPACE OpenMP

int main( int argc, char *argv[] )
{

    Kokkos::initialize(argc,argv);
    {

        if (argc != 2) {
            std::cout << "Please pass one integers on the command line" << std::endl;
        } else {
            // Initialize Kokkos
            int N = std::stoi(argv[1]);
            //
            // Default Execution Space is determined by the library-build time.
            // If the default is NVIDIA/AMD GPUs, you will get runtime eror
            Kokkos::View<double *> A_device("A_device", N); // Allocated in the Default Memory Space
            auto A_host = Kokkos::create_mirror_view(A_device);
            Kokkos::View<double *> B_device("B_device", N); // Allocated in the Default Memory Space
            auto B_host = Kokkos::create_mirror_view(B_device);
           
        

            // Execution on Default Space (it's device by default )
            Kokkos::parallel_for(Kokkos::RangePolicy<Kokkos::DefaultExecutionSpace>(0, N), KOKKOS_LAMBDA(const size_t index) {
                A_device(index) = static_cast<double>(index)*2.0; // A_device is altered
            });
#ifndef WITH_BUG
            Kokkos::deep_copy(A_host,A_device); // Need to sync between A_host and A_device
#endif
            // Execution on Serial Execution
            // You need to set -DKokkos_ENABLE_Serial=ON during the build time
            Kokkos::parallel_for(Kokkos::RangePolicy<Kokkos::Serial>(0, N), KOKKOS_LAMBDA(const size_t index) {
                B_host(index) = static_cast<double>(index)+A_host(index);
                // B_host is altered based on the value in A_host (A_host is copied from A_device)
            });
            
#ifndef WITH_BUG
            Kokkos::fence();
#endif

            // Execution on Default Space (it's device by default )
            Kokkos::parallel_for(Kokkos::RangePolicy<Kokkos::DefaultExecutionSpace>(0, N), KOKKOS_LAMBDA(const size_t index) {
                A_device(index) = A_device(index)-2.0;   // A_device is altered
            });
          
            // The next parallel_for needs the data from A_device.
#ifndef WITH_BUG
            Kokkos::deep_copy(B_device, B_host); // Kokkos_fence(); is sufficient if multiple devices can share the same memory space.
#endif
           
            Kokkos::parallel_for(Kokkos::RangePolicy<Kokkos::DefaultExecutionSpace>(0, N), KOKKOS_LAMBDA(const size_t index) {
                B_device(index) = B_device(index)+A_device(index);
            });

            Kokkos::deep_copy(B_host, B_device);
            Kokkos::deep_copy(A_host, A_device);

            for (int i = 0; i < N; ++i ) {
                std::cout << "A_host( " << i << " ) = " << A_host(i) << " : B_host( " << i << " ) = " << B_host(i) <<  std::endl; 
            }
        }
    }

    Kokkos::finalize();
    return 0;
}
