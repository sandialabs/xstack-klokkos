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
        int loop_count = 100;
        int league_size = 100;
        Kokkos::TeamPolicy<Kokkos::DefaultExecutionSpace> policy( league_size, Kokkos::AUTO);

        Kokkos::parallel_for( policy, KOKKOS_LAMBDA(member_type team_member)
        {
            int i = team_member.league_rank();
            parallel_for(Kokkos::TeamThreadRange<>(team_member, loop_count), [=] (int &j) {
                printf("Hello Wolrd %d %d\n",i,j);
            });

        });
    }

    Kokkos::finalize();
    return 0;
}