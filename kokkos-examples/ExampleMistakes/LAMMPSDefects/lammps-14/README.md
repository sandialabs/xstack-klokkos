LAMMPS git commit: d5418bd4632a3c94941ff429891548a054017664

Kokkos version 3.7

This is a seeded defect that is exposed when running the following simulation. 

examples/comb/in.comb.Cu

to replicate the defect, configure LAMMPS using OpenMP and Cuda backends seprately and enable the following packages while confguring LAMMPS:
-DPKG_KOKKOS=ON
-DEXTERNAL_KOKKOS=ON
-DPKG_MANYBODY=ON
-DPKG_BODY=ON
-DPKG_BPM=ON
-DPKG_COLLOID=ON
-DPKG_CORESHELL=ON
-DPKG_KSPACE=ON
-DPKG_MOLECULE=ON
-DPKG_RIGID=ON
-DPKG_ML-PACE=ON

to execute the simulation:

cmds to run:
OpenMP: 
cd examples/comb/
<path-to-lmp-executable> -k on t 1 -pk kokkos newton on neigh half -sf kk -in in.comb.Cu

Cuda:
cd examples/comb/
<path-to-lmp-executable> -k on g 1 -pk kokkos newton on neigh half -sf kk -in in.comb.Cu

Output of the above executions are stored in openmp.log and cuda.log files. To check the difference in the outputs use cmd:
`diff openmp.log cuda.log`

buggy source file path in LAMMPS:
src/KOKKOS/atom_vec_charge_kokkos.cpp

to check the patch run cmd:
`diff atom_vec_charge_kokkos-buggy.cpp atom_vec_charge_kokkos-fixed.cpp`

