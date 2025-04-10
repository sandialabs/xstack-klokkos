#include <iostream>
#include <vector>
#include <cmath>

#define PI 3.1415926535897932384

typedef int int_t;

//#include "Tile3D.h"
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

int main( int argc, char *argv[] )
{

   double cfl = 0.1; // must be less than 1/6
   int xsize=98, ysize=98, zsize=98;
   bool do_check_sum = true;

   std::vector<std::vector<std::vector<double>>> stencil_0;
   std::vector<std::vector<std::vector<double>>> stencil_1;

   stencil_0.resize(xsize+2);
   stencil_1.resize(xsize+2);
   for( int i = 0; i < xsize+2; ++i )
   {
      stencil_0[i].resize(ysize+2);
      stencil_1[i].resize(ysize+2);
      for ( int j = 0; j < ysize+2; ++j )
      {
         stencil_0[i][j].resize(zsize+2);
         stencil_1[i][j].resize(zsize+2);
      }
   }

   // Soft copy
   auto &stencil_old = stencil_0;
   auto &stencil_new = stencil_1;
   double checksum = 0;


   // Initialize stencil
   for (int i = 0; i < xsize + 2; ++i) {
      for (int j = 0; j < ysize + 2; ++j) {
         for (int k = 0; k < zsize + 2; ++k) {
            stencil_old[i][j][k]  = std::sin(1.0 * PI * (double) i / (double) (xsize + 1) )  ;
            stencil_new[i][j][k] =  stencil_old[i][j][k];
         }
      }
   }

   //
   // How to catch the error ... order matters.  where does the error come from?
   // Physical location could matter (plus interaction with OS)
   //

   // Original checksum
   if ( do_check_sum ) {
      for (int i = 1; i <= xsize; ++i) {
         for (int j = 1; j <= ysize; ++j) {
            for (int k = 1; k <= zsize; ++k) {
               checksum += stencil_old[i][j][k];
            }
         }
      }
   }

   std::cout << "Initial Checksum " <<  std::scientific << checksum <<  std::endl;

   for (int its = 0; its < 10; its++ )
   {
      //std::cout << " Point (0,0,0)  " << stencil_old[0][0][0] << std::endl;
      // std::cout << " Point (0,0,0)  " << stencil_new[0][0][0]  << std::endl;

      if( do_check_sum  ) {
         // Deduct the checksum from the boundary

         for (int k = 1; k <= zsize; ++k) {
            for (int j = 1; j <= ysize; ++j) {
               checksum -= left_flux(stencil_old[0][j][k], stencil_old[1][j][k], cfl)
                     + right_flux(stencil_old[xsize][j][k], stencil_old[xsize + 1][j][k], cfl);
            }
         }

         for (int k = 1; k <= zsize; ++k) {
            for (int i = 1; i <= xsize; ++i) {
               checksum -= left_flux(stencil_old[i][0][k], stencil_old[i][1][k], cfl)
                     + right_flux(stencil_old[i][ysize][k], stencil_old[i][ysize + 1][k], cfl);
            }
         }

         for (int j = 1; j <= ysize; ++j) {
            for (int i = 1; i <= xsize; ++i) {
               checksum -= left_flux(stencil_old[i][j][0], stencil_old[i][j][1], cfl)
                     + right_flux(stencil_old[i][j][zsize], stencil_old[i][j][zsize + 1], cfl);
            }
         }
      }




      // Apply stencil
      // Replace the loops by parallel for
      for (int i = 1; i <= xsize; ++i ) {
         for (int j = 1; j <= ysize; ++j) {
            for (int k = 1; k <= zsize; ++k) {
               //std::cout << "Old " << i << " " << j << " " << k << ": " <<  stencil_old(i,j,k) << std::endl;
               stencil_new[i][j][k] = stencil6p( stencil_old[i][j][k],
                                                 stencil_old[i-1][j][k],
                                                 stencil_old[i+1][j][k],
                                                 stencil_old[i][j-1][k],
                                                 stencil_old[i][j+1][k],
                                                 stencil_old[i][j][k-1],
                                                 stencil_old[i][j][k+1],
                                                 cfl );

            }
         }
      }

      double chk_ = 0;

      if(do_check_sum) {
         // computer alternative checksum and verify
         std::cout << "its " << its << std::endl;
         for (int i = 1; i <= xsize; ++i) {
            for (int j = 1; j <= ysize; ++j) {
               for (int k =1; k <= zsize; ++k) {
                  chk_ += stencil_new[i][j][k];
               }
            }
         }

         std::cout << "New Checksum " <<  std::scientific << chk_ << " and analytical checksum " << checksum <<  std::endl;
         // Testing the checksum
         auto error = std::abs((chk_ - checksum));
         if (error  > 1e-4) {
            std::cout << "Failed " << error << std::endl;
         }
      }
      // Alternate stencil assignment
      auto stencil_tmp =stencil_old;
      stencil_old = stencil_new;
      stencil_new = stencil_tmp;
   }
   // Final result is the values from stencil_new
   return 0;
}
