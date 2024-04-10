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
        // Use Team Policy

        // Default Execution Space
        typedef Kokkos::TeamPolicy<Kokkos::DefaultExecutionSpace>::member_type member_type;

        int league_size = 1000;  // of instances in the league level
        Kokkos::TeamPolicy<Kokkos::DefaultExecutionSpace> policy( league_size, Kokkos::AUTO()); // Use the predetermined team size for the given runtime

        Kokkos::parallel_for( policy, KOKKOS_LAMBDA(member_type team_member)
        {
            int i = team_member.league_rank() * team_member.team_size() + team_member.team_rank();
            printf("Hello Wolrd %d\n",i);
        });
    }

    Kokkos::finalize();
    return 0;
}