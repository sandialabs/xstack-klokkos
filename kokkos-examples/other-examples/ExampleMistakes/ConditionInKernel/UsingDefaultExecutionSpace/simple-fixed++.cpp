#include <cstdio>
#include <cstdlib>
#include <Kokkos_Core.hpp>
#include <cassert>

int main( int argc, char *argv[] )
{
    Kokkos::initialize(argc, argv);
    {
        Kokkos::View<double *> device_state("state",1);                    // view to store state on device (i.e. DefaultExecutionSpace)
        auto host_state = Kokkos::create_mirror(device_state);             // view to store state on host with same layout as device state

        host_state(0) = 1.0;                                               // initialize state in host view
        Kokkos::deep_copy(device_state, host_state);                       // copy initialized data in host state to device state

        Kokkos::parallel_for (1, KOKKOS_LAMBDA (const size_t i)  {
            device_state(i) = 2.0;                                         // suppose this is heavy computation, update the device state
        });

        auto updated_state = Kokkos::create_mirror_view(device_state);     // view to retrieve the updated device state
        Kokkos::deep_copy(updated_state, device_state);                    // copy updated final state from device to the final state on host

        std::cout<< "host:    ptr=" << host_state.data()    << ", on_host=" <<  host_state.is_hostspace    << ", #use=" << host_state.use_count()    << ", value=" << host_state(0) <<    std::endl;
        std::cout<< "device:  ptr=" << device_state.data()  << ", on_host=" <<  device_state.is_hostspace  << ", #use=" << device_state.use_count()  << std::endl;
        std::cout<< "updated: ptr=" << updated_state.data() << ", on_host=" <<  updated_state.is_hostspace << ", #use=" << updated_state.use_count() << ", value=" << updated_state(0) << std::endl;

        assert(host_state(0) != updated_state(0));                         // verify that host state is different from device state
    }
    Kokkos::finalize();
    return 0;
}
