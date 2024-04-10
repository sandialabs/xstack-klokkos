typedef double value_type;
typedef Kokkos::OpenMP   HostExecSpace;
typedef Kokkos::Cuda     DeviceExecSpace;
typedef Kokkos::RangePolicy<DeviceExecSpace>  device_range_policy;
typedef Kokkos::RangePolicy<HostExecSpace>    host_range_policy;
typedef Kokkos::View<double*, Kokkos::CudaSpace>   ViewVectorType;
typedef Kokkos::View<double**, Kokkos::CudaSpace>  ViewMatrixType;

// Setup data on host  
// use parameter xVal to demonstrate variability between iterations
void init_src_views(ViewVectorType::HostMirror p_x,
                  ViewMatrixType::HostMirror p_A,
                  const value_type xVal ) {
    
  Kokkos::parallel_for( "init_A", host_range_policy(0,N), [=] ( int i ) {
    for ( int j = 0; j < M; ++j ) {
      h_A( i, j ) = 1;
    }
  });

  Kokkos::parallel_for( "init_x", host_range_policy(0,M), [=] ( int i ) {
    h_x( i ) = xVal;
  });
}
  
ViewVectorType y( "y", N );
ViewVectorType x( "x", M );
ViewMatrixType A( "A", N, M );

ViewVectorType::HostMirror h_y = Kokkos::create_mirror_view( y );
ViewVectorType::HostMirror h_x = Kokkos::create_mirror_view( x );
ViewMatrixType::HostMirror h_A = Kokkos::create_mirror_view( A );
  
for ( int repeat = 0; repeat < nrepeat; repeat++ ) {
  init_src_views( h_x, h_A, repeat+1);  // setup data for next device launch
  
  Kokkos::fence(); // barrier used to synch between device and host before copying data
    
  // Deep copy host data needed for this iteration to device.
  Kokkos::deep_copy( h_y, h );
  Kokkos::deep_copy( x, h_x );
  Kokkos::deep_copy( A, h_A );  // implicit barrier

  // Application: y=Ax
  Kokkos::parallel_for( "yAx", device_range_policy( 0, N ), 
                              KOKKOS_LAMBDA ( int j ) {
    double temp2 = 0;
    for ( int i = 0; i < M; ++i ) {
      temp2 += A( j, i ) * x( i );
    }

    y( j ) = temp2;
  } );
    
  // note that there is no barrier here, so the host thread will loop
  // back around and call ini_src_views while the kernel is still running
}