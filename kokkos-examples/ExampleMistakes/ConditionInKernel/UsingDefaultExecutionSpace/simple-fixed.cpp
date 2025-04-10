#include <cstdio>
#include <cstdlib>
#include <Kokkos_Core.hpp>
#include <cassert>

#ifndef EXE_SPACE
#define EXE_SPACE DefaultExecutionSpace
#endif


int main( int argc, char *argv[] )
{
 	Kokkos::initialize(argc, argv);
	{
		Kokkos::View<double **, Kokkos::EXE_SPACE::memory_space> final_state("FINAL",1,1);  // view to store final state on device
		auto initial_state = Kokkos::create_mirror(final_state);  			    // view to store initial state on host having same dimensions as final state

		initial_state(0,0) = 1.0;							    // initialize data in initial state view
		Kokkos::deep_copy(final_state, initial_state);					    // copy initialized data in initial state to the final state

		typedef Kokkos::TeamPolicy<Kokkos::EXE_SPACE> Policy;
  	      	Policy policy(1,Kokkos::AUTO);
 		Kokkos::parallel_for (policy, KOKKOS_LAMBDA (Policy::member_type team)
        	{
			final_state(0,0) = 2.0;							   // suppose this is heavy computation, update the final state
        	});


		auto final_state_h = Kokkos::create_mirror_view(final_state);  			   // view to store final state on host
		Kokkos::deep_copy(final_state_h, final_state);				   	   // copy updated final state from device to the final state on host

		std::cout<< "initial state: " << initial_state(0,0) << std::endl;  		   // print initial state on host
		std::cout<< "final state: " << final_state_h(0,0) << std::endl;			   // print final state on host

		// verify that final state is different from initial state
		assert(initial_state(0,0) != final_state_h(0,0));
	}
	Kokkos::finalize();
	return 0;
}
