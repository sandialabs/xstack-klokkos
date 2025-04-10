This is a subset of the defects fixed in https://github.com/lammps/lammps/pull/3477.
"Fix issue in Kokkos MEAM where a host pointer was being used in device code (caused abort on GPUs)"

To replicate the defect, run the following cmd from inside `lammps/examples/meam` directory using LAMMPS binary built with kokkos enabled with CUDA back end. 
`lmp -in in.meam -pk kokkos newton on neigh half -k on g 1 -sf kk`
Pre-computed results are stored in `cuda.log`.  

To produce the expected output, run the following cmd from inside `lammps/examples/meam` directory using LAMMPS binary built with kokkos enabled with OpenMP+Serial back ends:
`lmp -in in.meam -pk kokkos newton on neigh half -k on t 1 -sf kk`
Pre-computed results are stored in `openmp.log`.  

To check the difference in the outputs use cmd:
`diff openmp.log cuda.log`

buggy source file path in LAMMPS:
src/KOKKOS/pair_meam_kokkos.cpp

to check the patch run cmd:
`diff pair_meam_kokkos-buggy.cpp pair_meam_kokkos-fixed.cpp`

