
#include <iostream>
#include <Kokkos_Core.hpp>

#define PI 3.1415926535897932384

typedef int int_t;

//#include "Tile3D.h"
KOKKOS_INLINE_FUNCTION double left_flux(double left, double self, double cfl)  {
   return   - cfl  * left + cfl * self;
}

KOKKOS_INLINE_FUNCTION double right_flux(double self, double right, double cfl)  {
   return   - cfl  * right + cfl * self;
}

KOKKOS_INLINE_FUNCTION double stencil6p(double self, double xm, double xp, double ym,
                                        double yp, double zm, double zp, double cfl )
{
   return ( 1.0 - 6.0 * cfl ) * self + cfl * (xm + xp + ym + yp + zm + zp);
}

int main( int argc, char *argv[] )
{

   double cfl = 0.1; // must be less than 1/6
   int xsize=98, ysize=98, zsize=98;
   bool do_check_sum = true;

   Kokkos::initialize(argc,argv);
   {
      Kokkos::View<double ***> stencil_0( "data1",xsize + 2,ysize + 2,zsize + 2);
      Kokkos::View<double ***> stencil_1( "data2",xsize + 2,ysize + 2,zsize + 2);

      // Soft copy
      auto stencil_old = stencil_0;
      auto stencil_new = stencil_1;
      auto stencil_tmp  = stencil_new;
      double checksum = 0;


      // Initialize stencil
      Kokkos::parallel_for("Loop: X-dimension",xsize+2, KOKKOS_LAMBDA(const int i)  {
         for (int j = 0; j < ysize + 2; ++j) {
            for (int k = 0; k < zsize + 2; ++k) {

               stencil_old(i, j, k) = std::sin(1.0 * PI * (double) i / (double) (xsize + 1)) ;
               stencil_new(i, j, k) =  stencil_old(i, j, k);
            }
         }
      });

      //
      // How to catch the error ... order matters.  where does the error come from?
      // Physical location could matter (plus interaction with OS)
      //

      // Original checksum
      if ( do_check_sum ) {
          Kokkos::parallel_reduce("Loop: X-dimension", Kokkos::RangePolicy<>(1,xsize+1),KOKKOS_LAMBDA(const int i, double &localSum)  {
             for (int j = 1; j <= ysize; ++j) {
                for (int k = 1; k <= zsize; ++k) {
                   localSum += stencil_old(i, j, k);
                }
             }
         },checksum);
      }
      std::cout << "Initial Checksum " <<  std::scientific << checksum <<  std::endl;

      for (int its = 0; its < 10; ++its )
      {
         //std::cout << " Point (0,0,0)  " << stencil_old(0,0,0) << " Point (32,40,0)  " << stencil_old (32,40,0) << std::endl;

         if( do_check_sum  ) {
            // Deduct the checksum from the boundary
            double addSum = 0;
            Kokkos::parallel_reduce("Loop: Z-dimension",Kokkos::RangePolicy<>(1,zsize+1), KOKKOS_LAMBDA(const int k, double &localSum)  {
               for (int j = 1; j <= ysize; ++j) {
                  localSum -= left_flux(stencil_old(0, j, k), stencil_old(1, j, k), cfl)
                              + right_flux(stencil_old(xsize, j, k), stencil_old(xsize + 1, j, k), cfl);
               }
            },addSum);
            checksum += addSum;
            addSum = 0;
            Kokkos::parallel_reduce("Loop: Z-dimension",Kokkos::RangePolicy<>(1,zsize+1), KOKKOS_LAMBDA(const int k, double &localSum)  {
               for (int i = 1; i <= xsize; ++i) {
                  localSum -= left_flux(stencil_old(i, 0, k), stencil_old(i, 1, k), cfl)
                              + right_flux(stencil_old(i, ysize, k), stencil_old(i, ysize + 1, k), cfl);
               }
            }, addSum);

            checksum += addSum;
            addSum = 0;
            Kokkos::parallel_reduce("Loop: Y-dimension",Kokkos::RangePolicy<>(1,ysize+1), KOKKOS_LAMBDA(const int j, double &localSum)  {
               for (int i = 1; i <= xsize; ++i) {
                  localSum -= left_flux(stencil_old(i, j, 0), stencil_old(i, j, 1), cfl)
                              + right_flux(stencil_old(i, j, zsize), stencil_old(i, j, zsize + 1), cfl);
               }
            }, addSum);
            checksum += addSum;
#if 0
            for (int k = 0; k <= zsize + 1; ++k) {
               checksum -= stencil_old(0, 0, k) + stencil_old(0, ysize + 1, k) +
                       stencil_old(xsize + 1, 0, k) + stencil_old(xsize + 1, ysize + 1, k);

            }

            for (int j = 1; j <= ysize; ++j) {
               checksum -= stencil_old(0, j, 0) + stencil_old(0, j, zsize + 1) +
                       stencil_old(xsize + 1, j, 0) + stencil_old(xsize + 1, j, zsize + 1);

            }

            for (int i = 1; i <= xsize; ++i) {
               checksum -= stencil_old(i, 0, 0) + stencil_old(i, 0, zsize + 1) +
                       stencil_old(i, ysize + 1, 0) + stencil_old(i, ysize + 1, zsize + 1);

            }
#endif

         }


         // std::cout << "Analytical Checksum " <<  std::scientific << checksum << std::endl;

         // Apply stencil
         // Replace the loops by parallel for
         //
         Kokkos::parallel_for("Loop: X-dimension", Kokkos::RangePolicy<>(1,xsize+1), KOKKOS_LAMBDA(const int i)  {
            for (int j = 1; j <= ysize; ++j) {
               for (int k = 1; k <= zsize; ++k) {
                  //std::cout << "Old " << i << " " << j << " " << k << ": " <<  stencil_old(i,j,k) << std::endl;
                  stencil_new(i,j,k) = stencil6p( stencil_old(i,j,k),
                          stencil_old(i-1,j,k),
                          stencil_old(i+1,j,k),
                          stencil_old(i,j-1,k),
                          stencil_old(i,j+1,k),
                          stencil_old(i, j,k-1),
                          stencil_old(i, j,k+1),
                          cfl );
#if 0
                  if( i == 1 && j == 1 && k == 1 )
                     std::cout << "New " << i << " " << j << " " << k << ": " <<
                     stencil_new(i,j,k) << "  OLD : " <<   stencil_old(i,j,k) <<  " : "
                     << stencil_old(i-1,j,k) << " : " << stencil_old(i+1,j,k) << " : "
                     << stencil_old(i,j-1,k) << " : " << stencil_old(i,j+1,k) << " : "
                     << stencil_old(i, j,k-1) << " : " << stencil_old(i, j,k+1) << std::endl;
#endif
               }
            }
         });

#if 0
         // Copy the boundary condition to stencil_new from stencil_old
            // Copy Y-Z planes
            for (int j = 0; j <= ysize+1; ++j) {
               for (int k = 0; k <= zsize+1; ++k) {
                  stencil_new(0,j,k) = stencil_old(0,j,k);
                  stencil_new(xsize+1,j,k) = stencil_old(xsize+1,j,k);
               }
            }

            // Copy X-Z planes
            for (int i = 0; i <= xsize+1; ++i) {
               for (int k = 0; k <= zsize+1; ++k) {
                  stencil_new(i,0,k) = stencil_old(i,0,k);
                  stencil_new(i,ysize+1,k) = stencil_old(i,ysize+1,k);
               }
            }

            // Copy X-Y Planes
            for (int i = 0; i <= xsize+1; ++i) {
               for (int j = 0; j <= ysize+1; ++j) {
                  stencil_new(i,j,0) = stencil_old(i,j,0);
                  stencil_new(i,j,zsize+1) = stencil_old(i,j,zsize+1);
               }
            }
#endif

         double chk_ = 0;

         if(do_check_sum) {
            double check_inc = 0;
            // computer alternative checksum and verify
             Kokkos::parallel_reduce("Loop: X-dimension", Kokkos::RangePolicy<>(1,xsize+1), KOKKOS_LAMBDA(const int i, double &localChk_)  {
               for (int j = 1; j <= ysize; ++j) {
                  for (int k =1; k <= zsize; ++k) {
                        localChk_+= stencil_new(i, j, k);
                  }
               }
            }, chk_);
            std::cout << "New Checksum " <<  std::scientific << chk_ << " and analytical checksum " << checksum <<  std::endl;
            // Testing the checksum
            auto error = std::abs((chk_ - checksum));
            if (error  > 1e-4) {
               std::cout << "Failed " << error << std::endl;
            }
         }
         // Alternate stencil assignment
         if (its % 2 == 0 )
         {
            stencil_old = stencil_1;
            stencil_new = stencil_0;
         } else {
            stencil_old = stencil_0;
            stencil_new = stencil_1;
         }
      }
   }

   Kokkos::finalize();
   return 0;
}
