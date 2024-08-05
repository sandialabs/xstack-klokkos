#include <cstdio>
#include <cstdlib>
#include <Kokkos_Core.hpp>
#include <Kokkos_DualView.hpp>

int main( int argc, char *argv[] )
{

    Kokkos::initialize(argc,argv);
    {
        int M, N;

        if (argc != 3) {
            M = 100;
            N = 1000;
        } else {
            M = std::stoi(argv[1]);
            N = std::stoi(argv[2]);
        }

        Kokkos::View <double **>       A("MatA",N,M);
        Kokkos::View <double *>        B("VecB",N);
        Kokkos::DualView <double *>    A_rowsum("Sum",N);

        Kokkos::deep_copy(B,1.0);
        Kokkos::deep_copy(A_rowsum.d_view,0.0);

        typedef Kokkos::TeamPolicy<>::member_type team_handle; // Use the default Execution Space
        Kokkos::parallel_for(Kokkos::TeamPolicy<>(N, Kokkos::AUTO, 4), KOKKOS_LAMBDA(const team_handle &team) {

            // Each team is assigned to each row of A
            int n = team.league_rank();

            Kokkos::parallel_for(Kokkos::TeamThreadRange(team, M), [&](const int &i) {
                A(n, i) = B(n) + static_cast<double>(i+n);
            });

#ifndef WITH_BUG
            // Needs a team barrier.  Otherwise, the cores in each team execute parallel_reduce without waiting for other cores...
            team.team_barrier();
#endif
            double team_sum; // This is declared within the execution space, indicating the local to the execution space.

            Kokkos::parallel_reduce(Kokkos::TeamThreadRange(team, M), [&](const int &i, double &lsum) {
                lsum += A(n, i);
            }, team_sum);

            //
            // Only one thread in each team executes this
            //
#ifdef WITH_BUG
            A_rowsum(n) += team_sum; // All the cores in the team update the value. No good!
#else
            Kokkos::single(Kokkos::PerTeam(team), [&]() {
                A_rowsum.d_view(n) += team_sum;
            });
#endif
        });

        // Verification
        Kokkos::deep_copy(A_rowsum.h_view,A_rowsum.d_view);
        bool flag = true;
        for (int i = 0; i < N; ++i )
        {

            if ( A_rowsum.h_view(i) != static_cast<double>(i*M+(M+1)*M/2) ) {

                std::cout << "Something is wrong at Row " << i << " Value " << A_rowsum.h_view(i) << " Expexcted Value "
                          << i * M + (M + 1) * M / 2 << std::endl;
                flag = false;
                break;
            }
            std::cout << "value ( " << i << " ) : " << A_rowsum.h_view(i) << std::endl;
        }
        if ( flag ) {
            std::cout << "Test Passed" << std::endl;
        } else {
            std::cout << "Test Failed" << std::endl;
        }
    }
}
