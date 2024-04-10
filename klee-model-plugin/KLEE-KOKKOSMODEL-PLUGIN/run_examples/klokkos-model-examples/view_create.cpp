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
    //klee_make_symbolic(&e_space, sizeof(ExeSpace), "exec space");
    //klee_assume((e_space ==  DefaultExeSpace) || (e_space == OmpExeSpace) || (e_space == CudaExeSpace));
    //klee_make_symbolic(&m_space, sizeof(MemSpace), "memory space");
    //klee_assume((m_space == DefaultMemSpace || m_space ==  CudaMemSpace || m_space == HipMemSpace || m_space == SyclMemSpace || m_space == HostMemSpace));
    KokkosView A = DeclareView( "View A", 1, input , 100, DOUBLE, m_space);
  }
  finalize();
  cout << "After DeclareView" << "\n";
  return 0;
}
