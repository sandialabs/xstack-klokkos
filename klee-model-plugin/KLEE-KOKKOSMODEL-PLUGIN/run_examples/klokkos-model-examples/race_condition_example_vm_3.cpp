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
    int input[1]  = {100};
    ExeSpace e_space;
    MemSpace m_space; 
    klee_make_symbolic(&e_space, sizeof(ExeSpace), "exec space");
    klee_assume((e_space ==  DefaultExeSpace) || (e_space == OmpExeSpace) || (e_space == CudaExeSpace));
    klee_make_symbolic(&m_space, sizeof(MemSpace), "memory space");
    klee_assume((m_space == DefaultMemSpace || m_space ==  CudaMemSpace || m_space == HipMemSpace || m_space == SyclMemSpace || m_space == HostMemSpace));
    KokkosView A = DeclareView( "View A", 1, input , 100, DOUBLE, m_space);
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
      klee_assume((i > 0 && i < 100));
      ParallelForRangePolicyBegin( i, 0, 100, e_space ); // Safe to assume it is GPU.
      auto MyFunc = [&](const int &i) 
      {
        int value = KokkosViewRead(A,i-1);
	KokkosViewAssign(A, i, value);  
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
      klee_assume((0 <= i ) && (i < 100));
      ParallelForRangePolicyBegin( i, 0, 100, SerialExeSpace ); 
      auto MyFunc = [&](const int &i) 
      {  
        int indices[1];
        indices[0] =i;
        KokkosViewAssign(A,i, indices[0]);
      };
      MyFunc(i);
      ParallelForRangePolicyEnd();  
    }

  }
  finalize();
  cout << "After All Done" << "\n";
  return 0;
}
