#include <cstdio>
#include <cstdlib>
#include <random>
#include <typeinfo>
#include <Kokkos_Core.hpp>
#include <Kokkos_Random.hpp>

// This examples aims at demonstrating out-of-bound view access with GPUs. 
// Since typical GPUs provide team of multiple threads (SIMD/WARP), it is important to care the out-of-bound access of some threads.
// For example, team_size=32 and N=100, one of the teams have only four threds accessing the view, and the rest of the threads are
// having out of bound access.

// For example,
// -DFIRST_EXE_SPACE=OpenMP
// -DSECOND_EXE_SPACE=Serial
//
// Another example,
// -DFIRST_EXE_SPACE=Cuda
// -DSECOND_EXE_SPACE=OpenMP

// Setting the execution space to Cuda. It can be HIP.
#ifndef FIRST_EXE_SPACE
//#define FIRST_EXE_SPACE Cuda
#define FIRST_EXE_SPACE Serial
#endif

// Setting the execution space to Cuda. It can be HIP.
#ifndef SECOND_EXE_SPACE
#define SECOND_EXE_SPACE Serial
//#define SECOND_EXE_SPACE Cuda
#endif


int main( int argc, char *argv[] )
{

    double lower_bound = 0;
    double upper_bound = 100;
    std::uniform_real_distribution<double> unif(lower_bound,upper_bound);
    std::default_random_engine re;
    
    Kokkos::initialize(argc,argv);
    {
        int nRows = 2000;
        int nCols = 4000;
        if (argc != 3) {
            std::cout << "Please pass two integers on the command line" << std::endl;  
        } else {
            nRows = atoi (argv[1]);
            nCols = atoi (argv[2]);
        }

        Kokkos::View<double **, Kokkos::FIRST_EXE_SPACE::memory_space> A("MAT_A",nRows,nCols);
        Kokkos::View<double *, Kokkos::FIRST_EXE_SPACE::memory_space> x("Vec_X",nCols);
        Kokkos::View<double *,Kokkos::FIRST_EXE_SPACE::memory_space> tmp("Vec_TMP",nRows);
        Kokkos::View<double *,Kokkos::SECOND_EXE_SPACE::memory_space> y("Vec_Y",nRows);
            
        //
        // Initialize
        // A, x and y
        //  
        auto A_m = Kokkos::create_mirror_view(A);
        auto x_m = Kokkos::create_mirror_view(x);
        auto y_m = Kokkos::create_mirror_view(y);
        for ( int iRow = 0; iRow < nRows; ++iRow)
        {
             y_m(iRow) = unif(re);
             for ( int iCol = 0; iCol < nCols; ++iCol ) 
             {
                 A_m(iRow,iCol) = unif(re);
                 x_m(iCol) = unif(re);
             }
         }

        Kokkos::deep_copy(A, A_m);
        Kokkos::deep_copy( x, x_m );
        Kokkos::deep_copy( y, y_m );

    
        auto tmp_m = Kokkos::create_mirror_view(tmp);
        typedef Kokkos::TeamPolicy<Kokkos::FIRST_EXE_SPACE> Policy;
        Policy policy(nRows,Kokkos::AUTO); // Using pre-set value for league, team partitions

        Kokkos::parallel_for (policy, KOKKOS_LAMBDA (Policy::member_type team)
        { 
            const auto iRow = team.team_size() * team.league_rank() +team.team_rank();
        // Without the if statement, the GPU code may fail as iRow can be greater than nRows    
        #ifndef WITH_BUG
            if( iRow >= nRows ) return;
        #endif
            tmp(iRow) = 0;
            Kokkos::parallel_reduce (Kokkos::ThreadVectorRange(team, nCols), [&] (int &iCol, double &local_x)
            {
                local_x += A(iRow,iCol) * x(iCol) ;
            }, tmp(iRow));
        });

        Kokkos::deep_copy(tmp_m,tmp); 

     
        double result = 0;
        if (typeid(y) != typeid(tmp) ) 
        {
            Kokkos::parallel_reduce( Kokkos::RangePolicy<Kokkos::SECOND_EXE_SPACE>(0,nRows), 
                KOKKOS_LAMBDA(const size_t &iRow, double & valueToUpdate )
                { 
                    valueToUpdate += y( iRow ) * tmp_m( iRow) ;
                }
            ,result);
        } else {
            Kokkos::parallel_reduce( Kokkos::RangePolicy<Kokkos::SECOND_EXE_SPACE>(0,nRows), 
                KOKKOS_LAMBDA(const size_t &iRow, double & valueToUpdate )
                { 
                    valueToUpdate += y( iRow ) * tmp( iRow) ;
                }
            ,result);
        }
        std::cout << "Result is " <<  std::scientific << result << std::endl;
    }

    Kokkos::finalize();
    return 0;
}
