#ifndef _KLOKKOS_KOKKOSMODEL_H
#define _KLOKKOS_KOKKOSMODEL_H
#include <string>
#include <array>
#include <vector>
#include <map>

namespace KModel {

  static int KModel_initalized = 0;
  // Can be multiple exectuion space 
 
   
  enum DataType { UINT, INT, FLOAT, DOUBLE, STRUCT };
  enum MemSpace { DefaultMemSpace, CudaMemSpace, HipMemSpace, SyclMemSpace, HostMemSpace };
  enum ExeSpace { DefaultExeSpace, CudaExeSpace, HipExeSpace, SyclExeSpace, OmpExeSpace, SerialExeSpace };
  enum MemLayout { DefaultLayout, LeftLayout, RightLayout };
  enum IndexType { INT64, INT32 };

  // Need to test the current execution space 
  // The ExeSpace for HIP, Cuda and SYCL are going to be multiple. 
  static ExeSpace KVM_exe_space = SerialExeSpace;
  static int      KVM_Cuda_space  = -1; // -1 is "not in this space", 0 or more means the ID for CudaSpace 
  static int      KVM_Hip_space   = -1; // -1 is "not in this space", 0 or more means the ID for HipSpace
  static int      KVM_Sycl_space  = -1; // -1 is "not in this space", 0 or more means the ID for SyclSpace
  static int      KVM_Omp_space   = -1; // -1 is "not in this space",

  // void report_uninitialized(  )

  /* It may not be necessary if we implement the virtual machine in C++ (KLEE does not do any analysis) */
  void initialize(int &argc, char* argv[] );

  void finalize();

  struct KokkosView
  {
    public:
    /* Flag indicating where the view is excuted. */
    bool inside_parallel_range_policy;
    bool inside_parallel_team_policy;
    bool inside_team_thread;
    bool inside_thread_vector;
    bool inside_per_thread_single;
    bool inside_per_team_single;
    
    int nDim;

    std::array<int64_t,9> indices = {0,0,0,0,0,0,0,0,0};
    std::string viewName;
    DataType data_type;
    MemSpace mem_space;
    MemLayout mem_layout;

    bool has_parent_view;
    KokkosView  *parent_view;  // Pointing parent KokkosView for reference. 

    // May need a list of views referring me

    // Race map is initailized at fence(), the beginning of an OpenMP execution space or team_barrier call (just for team)
    std::map<std::array<int,9>,int> race_map;
  };
 
  void ParallelForRangePolicyBegin( KokkosView &in,  int64_t start, int64_t end, ExeSpace espace  ) ;
  void ParallelForRangePolicyEnd( KokkosView &in, ExeSpace espace );

  KokkosView DeclareView( std::string name, int ndim, int *indices, DataType dtype, MemSpace mspace, MemLayout mlayout );
  KokkosView DeclareView( KokkosView &A ); // Based on referencing/softcopy. 
  KokkosView DeclareView( KokkosView &A, MemSpace mspace, MemLayout mlayout ); // Based on referencing/softcopy. 
 

  void deep_copy_const( KokkosView &dst, DataType dtype );
  void deep_copy( KokkosView &dst, KokkosView &src);
#if 0
  // Specifying execution space allows Asynchronous deep_copy
  // You need to call fence explicitly or deep_copy/parallel_reduce that make a implicit fence.
  void deep_copy( ExeSpace espace, KokkosView &dst, DataType dtype);
  void deep_copy( ExeSpace espace, KokkosView &dst, KokkosView &src);
#endif


#if 0
  KokkosView SubView ( KokkosView &A );

  void ParallelForTeamPolicyTopBegin( KokkosView &in, team_policy &policy ) ;
  void ParallelForTeamPolicyTopEnd( KokkosView &in, team_policy &policy );

  void ParallelForTeamPolicyTeamThreadBegin( KokkosView &in, team_policy &policy );
  void ParallelForTeamPolicyTeamThreadEnd( KokkosView &in,  team_policy &policy );

  void ParallelForTeamPolicyThreadVectorBegin( KokkosView &in,  team_policy &policy);
  void ParallelForTeamPolicyThreadVectorEnd( KokkosView &in,  team_policy &policy );

  void PerTeamSingleBegin( KokkosView &in, team_policy &policy );
  void PerTeamSingleEnd( KokkosView &in,team_policy &policy);

  void PerThreadSingleBegin( KokkosView &in, team_policy &policy );
  void PerThreadSingleEnd( KokkosView &in, team_policy &policy );

#endif

  void KokkosViewRead( KokkosView &in, int dim, int *indices, int thread_rank );
  void KokkosViewAssgin( KokkosView &in, int dim, int *indices, int thread_rank );
 

#if 0
  void KokkosTeamBarrier( KokkosView &in );

  // Since Kokkos leaves the its own value type's assingment operators, we use compiler to transform to the function below.
  void KokkosViewAssgin( KokkosView &in, int dim, int *index, int thread_rank );

  // These operations (++ and -- ) can be transltated by compiler to A++ => A=A+1;  A-- => A=A-1;  These functions may not necessary

  void KokkosViewPreIncrement(  KokkosView &in, int dim, int *index, int thread_rank  );

  void KokkosViewPostInrement( KokkosView &in, int dim, int *index, int thread_rank );

  void KokkosViewPreDecrement( KokkosView &in, int dim, int *index, int thread_rank  );
  
  void KokkosViewPostDecrement( KokkosView &in, int dim, int *index, int thread_rank  );

  void KokkosViewAddAssign(  KokkosView &in, int dim, int *index, int thread_rank  );

  void KokkosViewSubtractAssign(  KokkosView &in, int dim, int *index, int thread_rank  );

  void KokkosViewMultiplyAssign(  KokkosView &in, int dim, int *index, int thread_rank  );

  void KokkosViewDivideAssign(  KokkosView &in, int dim, int *index, int thread_rank  );

  void KokkosViewModAssign(  KokkosView &in, int dim, int *index, int thread_rank );

  void KokkosViewXORAssign(  KokkosView &in, int dim, int *index, int thread_rank  );

  void KokkosViewAndAssign( KokkosView &in, int dim, int *index, int thread_rank  );

#endif
} // end of namespace
#endif

