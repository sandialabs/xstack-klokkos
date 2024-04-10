#include <cstdio>
#include "KokkosVM_Core2.hpp"
#include "klee/klee.h"
#include <cstdio>
#include <iostream>


using namespace std;
using namespace KVM;

int main(int argc, char **argv)
{
  initialize(argc,argv);
  {
    int input[1]  = {100};
    ExeSpace e_space;
    MemSpace m_space;
    klee_make_symbolic(&e_space, sizeof(ExeSpace), "exec space");
    klee_assume((e_space ==  DefaultExeSpace) || (e_space == OmpExeSpace) || (e_space == CudaExeSpace));
    KokkosView A = DeclareView( "View A", 1, input , DOUBLE, m_space, LeftLayout);
    // This piece is equivalent to:
    // Kokkos::parallel_for( 100, KOKKOS_LABMDA( const int &i )
    // { 
    //    A(i) == non_kokkos_values;
    // } );
    {
      ParallelForRangePolicyBegin( A, 0, 100, e_space ); // Safe to assume it is GPU.
      // I suggest we should internally (in KLEE) keep the table for individual parallel_for
      int i;
      // The code generator automatically create the next two statements based on the values passed to the range policy.
      klee_make_symbolic(&i, sizeof(int), "parallel_for_0");
      //klee_assume((0 <= i ) && (i < 100));
      auto MyFunc = [&](const int &i) 
      {  
        int indices[1];
        indices[0] = i + 1;
        KokkosViewAssgin(A,1,indices,i);
      };
      MyFunc(i);
      ParallelForRangePolicyEnd( A, DefaultExeSpace );  
    }
    cout << "After first ParallelFor" << "\n";
    // This piece is equivalent to:
    // Kokkos::parallel_for( Kokkos::RangePolicy<Kokkos::Serial>(), KOKKOS_LABMDA( const int &i )
    // { 
    //    A(i) == non_kokkos_values;
    // } );
    // May not need to say the execution space (maintain in a stack to indicate this is matching call). 
    {
      ParallelForRangePolicyBegin( A, 0, 100, SerialExeSpace ); 
      // I suggest we should internally (in KLEE) keep the table for individual parallel_for
      int i;
      // The code generator automatically create the next two statements based on the values passed to the range policy.
      klee_make_symbolic(&i, sizeof(int), "parallel_for_1");
      //klee_assume((0 <= i ) && (i < 100));
      auto MyFunc = [&](const int &i) 
      {  
        int indices[1];
        indices[0] =i;
        KokkosViewAssgin(A,1,indices,i);
      };
      MyFunc(i);
      ParallelForRangePolicyEnd( A, DefaultExeSpace );  
    }

  }
  finalize();
  cout << "After All Done" << "\n";
  return 0;
}
