#include <cstdio>
#include "Kokkos_Model.hpp"
#include "klee/klee.h"
#include <cstdio>
#include <iostream>


using namespace std;
using namespace KModel;

int main(int argc, char **argv)
{
  initialize(argc,argv);
  {
    int size = 100;
    int input[1]  = {size};
    ExeSpace e_space;
    MemSpace m_space;
    klee_make_symbolic(&e_space, sizeof(ExeSpace), "exec space");
    klee_assume((e_space ==  DefaultExeSpace) || (e_space == OmpExeSpace) || (e_space == CudaExeSpace));
    KokkosView A = DeclareView( "View A", 1, input,size,DOUBLE, m_space);
    // This piece is equivalent to:
    // Kokkos::parallel_for( 100, KOKKOS_LABMDA( const int &i )
    // { 
    //    A(i) == non_kokkos_values;
    // } );
    {
      // I suggest we should internally (in KLEE) keep the table for individual parallel_for
      int i;
      // The code generator automatically create the next two statements based on the values passed to the range policy.
      klee_make_symbolic(&i, sizeof(int), "parallel_for_0");
      klee_assume((0 <= i ) && (i < 100));
      ParallelForRangePolicyBegin( i, 0, 100, e_space ); // Safe to assume it is GPU.
      auto MyFunc = [&](const int &i) 
      {
	A[i]=A[i-1];  
      };
      MyFunc(i);
      ParallelForRangePolicyEnd();  
    }
    cout << "After first ParallelFor" << "\n";
    // This piece is equivalent to:
    // Kokkos::parallel_for( Kokkos::RangePolicy<Kokkos::Serial>(), KOKKOS_LABMDA( const int &i )
    // { 
    //    A(i) == non_kokkos_values;
    // } );
    // May not need to say the execution space (maintain in a stack to indicate this is matching call). 
    {
      // I suggest we should internally (in KLEE) keep the table for individual parallel_for
      int i;
      // The code generator automatically create the next two statements based on the values passed to the range policy.
      klee_make_symbolic(&i, sizeof(int), "parallel_for_1");
      klee_assume((0 <= i ) && (i < size));
      ParallelForRangePolicyBegin( i, 0, size, SerialExeSpace ); 
      auto MyFunc = [&](const int &i) 
      {  
        int indices[1];
        indices[0] =i;
        KokkosViewAssgin(A,1,indices,i);
      };
      MyFunc(i);
      ParallelForRangePolicyEnd();  
    }

  }
  finalize();
  cout << "After All Done" << "\n";
  return 0;
}
