//
// Created by Teranishi, Keita on 2/28/22.
//
#include <stdio>
#include "/Users/knteran/openmpi-4.1.1/include/mpi.h"
#include <Kokkos_Core.hpp>


inline double left_flux(double left, double self, double cfl)  {
    return   - cfl  * left + cfl * self;
}

inline double right_flux(double self, double right, double cfl)  {
    return   - cfl  * right + cfl * self;
}

inline double stencil6p(double self, double xm, double xp, double ym,
                        double yp, double zm, double zp, double cfl )
{
    return ( 1.0 - 6.0 * cfl ) * self + cfl * (xm + xp + ym + yp + zm + zp);
}


int main ( int argc, char **argv)
{
    MPI_Comm mycomm;
    size_t num_ranks;
    size_t nObjSize_X = 2;
    size_t nObjSize_Y = 2;
    size_t nObjSize_Z = 2;
    size_t leftRank,rightRank,upRank,downRank,frontRank,backRank;
    size_t local_x_size = 64;
    size_t local_y_size = 64;
    size_t local_z_size = 64;

    MPI_Init( &argc, &argv );
    MPI_Comm_dup( MPI_COMM_WORLD, &mycomm );
    MPI_Comm_size( &num_ranks, mycomm);

    //
    // Input Handling
    //

    Kokkos::initialize(argc,argv);
    {
        // Compute 3D mapping
        //

        Kokkos::View<double ***> stencil_old;
        Kokkos::View<double ***> stencil_new;
        Kokkos::resize(stencil_old, local_x_size + 2, local_y_size + 2, local_z_size + 2);
        Kokkos::resize(stencil_new, local_x_size + 2, local_y_size + 2, local_z_size + 2);

        // Initialize the values

        // Copy the value to the host view

        for (size_t ts = 0; ts < num_timesteps; ts++) {
            Kokkos::parallel_for("Loop: X-dimension", Kokkos::RangePolicy<>(1, xsize + 1), KOKKOS_LAMBDA(const int i) {
                //
                //  Exchange ghost points
                //

                for (int j = 1; j <= local_y_size; ++j) {
                    for (int k = 1; k <= local_z_size; ++k) {
                        //std::cout << "Old " << i << " " << j << " " << k << ": " <<  stencil_old(i,j,k) << std::endl;
                        stencil_new(i, j, k) = stencil6p(stencil_old(i, j, k),
                                                     stencil_old(i - 1, j, k),
                                                     stencil_old(i + 1, j, k),
                                                     stencil_old(i, j - 1, k),
                                                     stencil_old(i, j + 1, k),
                                                     stencil_old(i, j, k - 1),
                                                     stencil_old(i, j, k + 1),
                                                     cfl);
                    }
                }
            });
            //
            // Post receive (IRecv) 6 directions  to the neighbors
            //
            // Send ghost points to the 6 neighbors
            MPI_WaitAll();
        }
    }
    Kokkos::finalize();
    MPI_Finalize();
}