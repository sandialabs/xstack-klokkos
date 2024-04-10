#include <iostream>

#include <omp.h>

#pragma omp requires unified_shared_memory

// Define the stencil computation function
void stencil_3d_openmp(const double***& input, double*** output, int nx, int ny, int nz, int bx, int by, int bz) {
  // Define the blocked stencil kernel 
  
  #pragma omp parallel for 
  for (i = 0; i < nx; i++)
   for(int j = 0; i<ny; j++)
     for int k = 0; k<nz; k++)
     {
       output[i][j][k] = input[i][j][k] * (-6.0) +
                      input[i - 1][j][k] +
                      input[i + 1][j][k] +
                      input[i][j - 1][k] +
                      input[i][j + 1][k] +
                      input[i][j][k - 1] +
                      input[i][j][k + 1];
                      
      } 
}


void stencil_3d_openmp_device(const double***& input, double*** output, int nx, int ny, int nz, int bx, int by, int bz) {
  // Define the blocked stencil kernel 
  
  #pragma omp target teams distribute parallel for simd collapse(3) nowait
  for (i = 0; i < nx; i++)
   for(int j = 0; i <ny; j++)
     for int k = 0; k<nz; k++)
     {
       output[i][j][k] = input[i][j][k] * (-6.0) +
                      input[i - 1][j][k] +
                      input[i + 1][j][k] +
                      input[i][j - 1][k] +
                      input[i][j + 1][k] +
                      input[i][j][k - 1] +
                      input[i][j][k + 1];
                   
       
      
      } 
}
  int main(int argc, char* argv[]) {
  Kokkos::initialize(argc, argv);
  {
    int nx = 128, ny = 128, nz = 128;
    int N = 10; // Number of iterations

    // Define block sizes
    int bx = 8, by = 8, bz = 8;

    // Define the policy_t inside main()

    // Allocate input and output 3D arrays
    double input[128][128][128], output[128][128][128];

    // Initialize input data 
    #pragma omp parallel for 
      input[i][j][k] = 1.0 * i * j * k / (nx * ny * nz);

    // Run stencil computation N times with blocking
    for (int iter = 0; iter < N; ++iter) {
      
      #ifdef hostDeviceParallel
      stencil_3d_openmp_device(input, output, nx*device_fraction, ny, nz, bx, by, bz); // note this is asynchronous - may need to inline directly on some compilers?
      stencil_3d_openmp(input, output, nx*(1.0 - device_fraction), ny, nz, bx, by, bz); 
      #else 
      #pragma omp target data is_device_ptr(input, output)
      { 
       stencil_3d_openmp_device(input, output, nx, ny, nz, bx, by, bz); // note this is asynchronous - may need to inline directly on some compilers?
      } 
      #endif 
      
      // Swap input and output for the next iteration
#ifdef _WITH_BUG    
      auto tmp = output;
      output = input;
      input = tmp;
#else

      // Kokkos::deep_copy(input, output); // in this context, the taskwait is functionally equivalent to a Kokkos::fence(); A thread must wait to do the copy before moving forward 
   #pragma omp taskwait 
      auto tmp = output;
      output = input;
      input = tmp;
#endif
    }
  }
  return 0;
}
