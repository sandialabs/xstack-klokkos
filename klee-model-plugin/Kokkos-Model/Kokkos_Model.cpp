#include <cstdio>
#include "Kokkos_Model.hpp"
#include <cstdio>


namespace KModel
{
 
  // Update global variable 
  void initialize(int &argc, char *argv[]) 
  {
    KModel_initalized = 1;
  }

  void finalize() {
    KModel_initalized = 0;
  }

  void deep_copy_const( KokkosView &dst, DataType dtype )
  {
    if ( KModel_initalized == 0)
    {
      fprintf(stderr, "Error at %s. Never initialized\n",__func__);
    }
    // Deep Copy always fences with other devices.
    // Do we need any special checking?
  }

  void deep_copy( KokkosView &dst, KokkosView &src)
  {
    if ( dst.nDim != src.nDim )
    {
      // Assertion!  
      fprintf(stderr, "deep_copy error. The view sizes are not the same\n");
    }
    // Deep Copy always fences with other devices.
    // Do we need any special checking?
    if( dst.mem_space ==  src.mem_space )
    {
      // Copy in the same device 

    } else {
      // Copy in the different device

    }
  }

  #if 0
  void deep_copy_const( ExeSpace exesp, KokkosView &dst, DataType dtype )
  {
    // Intended for Asynchronous copy
    // Need other fence calls to ensure the completion.
  }

  void deep_copy( ExeSpace exesp, KokkosView &dst, KokkosView &src)
  {
    // Intended for Asynchronous copy
    // Need other fence calls to ensure the completion.
    if ( dst.nDim != src.nDim )
    {
      // Assertion!  
      fprintf(stderr, "deep_copy error. The view sizes are not the same\n");
    }

    // Do we need any special checking?
    if( dst.mem_space ==  src.mem_space )
    {
      // Copy in the same device 

    } else {
      // Copy in the different device

    }
  }

  #endif 
  KokkosView DeclareView( std::string name, int ndim, int *indices, 
  DataType dtype, MemSpace mspace, MemLayout mlayout ) 
  {
    KokkosView output;
    output.inside_parallel_range_policy = false;
    output.inside_parallel_team_policy = false;
    output.inside_team_thread = false;
    output.inside_thread_vector = false;
    output.inside_per_thread_single = false;
    output.inside_per_team_single = false;
    output.nDim = ndim;
    output.viewName = name;
    output.data_type = dtype;
    output.mem_space = mspace;
    output.mem_layout = mlayout;
    output.has_parent_view = false;
    for ( int i = 0; i < ndim; i++ )
    {
      output.indices[i]=indices[i];
    }
    return output;
  }

  

  KokkosView DeclareView( KokkosView &in ) // Should we put size?
  {
    // This is softcopy
    KokkosView output = in;
    // output.parent_view = in; // 
    output.has_parent_view = true;
    output.mem_space = in.mem_space;
    return output;
  }


  KokkosView CreateMirrorView(KokkosView &in)
  {
    KokkosView output = in;
    output.mem_space = HostMemSpace;
    return output;
  }
  

  //
  //  I assume that we are making multiple calls to register KokkosView.  Does it make sense?
  //
  void ParallelForRangePolicyBegin( KokkosView &in,  int64_t start, int64_t end, ExeSpace espace  ) 
  {
     in.inside_parallel_range_policy = true;  
     // Initialize the table for access/ownership for the view
     //
     // The ownership is determined by the read and write indices derived from thread id
     //
     
  }

  void ParallelForRangePolicyEnd( KokkosView &in, ExeSpace espace )
  {
    in.inside_parallel_range_policy = false;
    // Reset the access/ownership table for the view.
    
  }



#if 0
  void ParallelForTeamPolicyTopBegin( KokkosView &in, team_policy &policy )
  {
    in.inside_parallel_team_policy = true;

  }

  void ParallelForTeamPolicyTopEnd( KokkosView &in, team_policy &policy )
  {
    in.inside_parallel_team_policy = false;
  }

  void ParallelForTeamPolicyTeamThreadBegin( KokkosView &in, team_policy &policy )
  {
    in.inside_parallel_team_thread = true;

  }

  void ParallelForTeamPolicyTeamThreadEnd( KokkosView &in, team_policy &policy )
  {
    in.inside_parallel_team_thread = false;
  }


  void ParallelForTeamPolicyThreadVectorBegin( KokkosView &in )
  {
    in.inside_parallel_thread_vector = true;

  }

  void ParallelForTeamPolicyThreadVectorEnd( KokkosView &in )
  {
    in.inside_parallel_thread_vector = flase;
  }

 
  void PerTeamSingleBegin( KokkosView  &in )
  {
    in.inside_per_team_single= true;

  }

  void PerTeamSingleEnd(  KokkosView  &in  )
  {
    in.inside_per_team_single = flase;

  }
  void PerThreadSingleBegin(  KokkosView  &in  )
  {
    in.inside_per_thread_single = true;

  }

  void PerThreadSingleEnd(  KokkosView  &in  )
  {
    in.inside_per_thread_single = false;

  }
#endif
  void KokkosViewRead( KokkosView &in, int dim, int *indices, int thread_rank )
  {
  #ifdef KLOKKOS_DEBUG
    /* Put assertion or any logging statement */
    printf("KokkosParallelForRangeEnd %d\n", __LINE__);
  #endif

    if( in.nDim != dim ) {
        printf("error\n");  // Assertion say something to KLEE
        return ;
    }
    /* Check boundary */
    for ( int i = 0 ; i < dim; i++ )
    {
      // Should we assert?
      if( in.indices[i] <= indices[i] )  // We want to KLEE to triger this as assertion
      {
        printf("Error out of bound access\n"); 
        return ;
      }
    } 


    /* Check race condition */
    // Use hash to convert a set of 9 indices into a single value
    // If different array indices are used to access (read-write, or write-read) to the same Kokkos::View, itt is going to be race.
    // If different array indices are used just read the same Kokkos::View, it is OK as long as no write operation is performed.
    //
    // B(i+4) = ... ;
    // A = B(i+2);   This is not OK.
    //
    // A = B(i+2);
    // B(i+4) = ...;    This is not OK as B(i+2) might be overwritten by other threads.
    //
    // B(i+4) = ... ;
    // A = B(i+4);   This is fine.
    //
    //
    // A = B(i+4);
    // C = B(i+11); This is fine
    // 
    //  TODO: put some information to SMT solver to define this read with indices 
    //  must come before/after the "write" to the same object.
    //
  }


  void KokkosViewAssign( KokkosView &in, int dim, int *indices, int thread_rank)
  {

  #ifdef KLOKKOS_DEBUG
    /* Put assertion or any logging statement */
    printf("KokkosParallelForRangeEnd %d\n", __LINE__);
  #endif

    if( in.nDim != dim ) {
        printf("error\n");  // Assertion to say something to KLEE
        return ;
    }
    /* Check boundary */
    for ( int i = 0 ; i < dim; i++ )
    {
      // Should we assert?
      if( in.indices[i] <= indices[i] )  // We want KLEE to trigger this as assertion
      {
        printf("Error out of bound access\n"); 
        return ;
      }
    } 

    // Check the execution space
    if ( in.inside_parallel_range_policy == false ) // We want to KLEE to triger this as assertion
    {
      if( in.mem_space != HostMemSpace)
      {
         printf("Error accesing the view through invalid execution space\n");
      }
    } else {
       if( in.mem_space == HostMemSpace)
       {
          // It is OK!
       }
    }
    
    /**************************************/
    /* Check input data type              */
    /* Kokkos is C++. It is not necessary */
    /**************************************/

    /* Check race condition */
    // Use hash to convert a set of 9 indices into a single value
    // If different array indices are used to access (read and write) to the same Kokkos::View, itt is going to be race.
    // If different array indices are used just read the same Kokkos::View, it is OK.
    #if 0
    std::map<std::array<int, 9>,int>::iterator it;

    it = in.race_map.find(indices);
    if (it == in.race_map.end())  {
      in.race_map[indices] = thread_rank;
    } else  {
      if(in.race_map[indices] != thread_rank) {
          printf("Race Condition! accesing %d by thread %d and %d\n",indices[0], in.race_map[indices], thread_rank);
      }
    } 
  #endif
    return ;
  }   

#if 0
void KokkosAdd( KokkosView *in, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
void KokkosSubtract( KokkosView *in, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
void KokkosMultiply( KokkosView *in, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
void KokkosDivide( KokkosView *in, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
void KokkosAddAssign( KokkosView *i:n, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
void KokkosSubtractAssign( KokkosView *in, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
void KokkosMultiplyAssign( KokkosView *in, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
void KokkosDivideAssign( KokkosView *in, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
void KokkosPreIncrement( KokkosView *in, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
void KokkosPostIncrement( KokkosView *in, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
void KokkosPreDecrement( KokkosView *in, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
void KokkosPostDecrement( KokkosView *in, int dim, int *index, int thread_rank, klokkos_view_data_t dtype );
#endif
}

