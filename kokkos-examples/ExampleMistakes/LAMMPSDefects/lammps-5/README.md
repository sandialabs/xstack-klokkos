LAMMPS git commit: d5418bd4632a3c94941ff429891548a054017664

Kokkos version 3.7

This defect is described in:
https://github.com/lammps/lammps/issues/3732

to execute the simulation use cmds:

OpenMP: 
`./lmp -k on t 1 -sf kk -pk kokkos newton on neigh half -in bug-3732.in`

Cuda
`./lmp -k on g 1 -sf kk -pk kokkos newton on neigh half -in bug-3732.in`

Output of the above executions are stored in openmp.log and cuda.log files. To check the difference in the outputs use cmd:
`diff openmp.log cuda.log`

buggy source file path in LAMMPS:
src/KOKKOS/pair_pace_kokkos.cpp

to check the patch run cmd:
`diff pair_pace_kokkos-buggy.cpp pair_pace_kokkos-fixed.cpp`

