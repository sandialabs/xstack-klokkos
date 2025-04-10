#include <iostream>
#include <Kokkos_Core.hpp>

#define N 2

int main(int argc, char * argv[]) {
  Kokkos::initialize(argc,argv);
  {
    Kokkos::View<int *> view("V", N);
    Kokkos::TeamPolicy<> policy(N, Kokkos::AUTO);
    Kokkos::parallel_for(policy, KOKKOS_LAMBDA(Kokkos::TeamPolicy<>::member_type team) {
      const auto index = team.team_size() * team.league_rank() + team.team_rank();
#ifndef WITH_BUG
      if (index < N) {
#endif
        view(index) = index;
#ifndef WITH_BUG
      }
#endif
    });
  }
  Kokkos::finalize();
  return 0;
}
