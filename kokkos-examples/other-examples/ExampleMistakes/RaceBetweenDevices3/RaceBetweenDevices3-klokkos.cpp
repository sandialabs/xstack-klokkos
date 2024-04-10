#include <iostream>
#include "Kokkos_Model.h"
#include <klee/klee.h>

int main(argc, argv)
{
  initialize(argc,argv);
  {

    int nx = 128, ny = 128, nz = 128;
    int N = 10; // Number of iterations

    // Define block sizes
    int bx = 8, by = 8, bz = 8;

    // Define the policy_t inside main()

    int input[1]  = {nx};
// Todo: change to 1.0*i*j*k / (nx*ny*nz);

    ExeSpace e_space;
    MemSpace m_space; 
    klee_make_symbolic(&e_space, sizeof(ExeSpace), "exec space");
    klee_assume((e_space ==  DefaultExeSpace) || (e_space == OmpExeSpace) || (e_space == CudaExeSpace));
    KokkosView A = DeclareView( "View A", 1, input , DOUBLE, m_space, LeftLayout);
   KokkosView B = DeclareView( "View B", 1, input , DOUBLE, m_space, LeftLayout);

 // This piece is equivalent to:
    // Kokkos::parallel_for( 128, KOKKOS_LABMDA( const int &i )
    // { 
    //    A(i) == non_kokkos_values;
// B(i) == non_kokkos_values;

    // } );
    {
for(int tstep=0; tstep < N; tstep++)
{
      ParallelForRangePolicyBegin( A, 0, 100, e_space ); // Safe to assume it is GPU.
      int i; 
      // Source translation (or tools callback?) automatically create the next two statements based on the values passed to the range policy.
      klee_make_symbolic(&i, sizeof(int), "parallel_for_0");
      // klee_assume((0 <= i ) && (i < nx));
     
      auto MyFunc = [&](const int &i) 
      {  
        int indices[3];
        indices[0] =i-1;
        indices[1] = i;
        indices[2] = i+1;
        double borderLeft, borderRight, centerVal;
        KokkosViewRead(borderLeft, A, 1, indices[0]);
        KokkosViewRead(borderRight, A, 1, indices[2]);
        KokkosViewRead(centerVal, A, 1, indices[1]);
// Todo: need to figure out MDSpan conversion/use here? 
// Don't use either of these two functions for now
        ///KokkosViewAdd(A, 1, indices[2], indices[0]));
       // KokkosViewIncrement(outputSum, A, 1, indices[1]); 
        
        KokkosViewAssgin(B,1,indices,(borderLeft+ borderRight+ centerVal)/3.0);
      };
      MyFunc(i);
      ParallelForRangePolicyEnd( A, DefaultExeSpace );  
   #ifdef _WITH_BUG 
      auto tmp = B;
      B = A;
      A = B;
#else
   // KokkosFence();
    KokkosDeepCopy(A, B);
    Kokkos::deep_copy(input, output);
      auto tmp = B;
      B = A;
      A = B;
#endif

 } // end timestep loop 

   } // end block
finalize();
return 0; 

} // end main 
   
