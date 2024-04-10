LAMMPS git commit: d5418bd4632a3c94941ff429891548a054017664

Kokkos version 3.7

This is a seeded defect that is exposed when running the following simulation. 
We modify the input script to run the simulation for more steps (set run 40000 and thermo 1000) to make the divergent results noticiable. 
Numerical differences start to appear from step 2000, and the differences are large for some instances e.g., "Press" at step 6000 (0.35624779 vs 1.1372686).

/examples/balance/in.balance

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
cd examples/balance/
<path-to-lmp-executable> -k on t 1 -pk kokkos newton on neigh half -sf kk -in in.balance

Cuda:
cd examples/balance/
<path-to-lmp-executable> -k on g 1 -pk kokkos newton on neigh half -sf kk -in in.balance

Output of the above executions are stored in openmp.log and cuda.log files. To check the difference in the outputs use cmd:
`diff openmp.log cuda.log`

buggy source file path in LAMMPS:
src/KOKKOS/pair_lj_cut_kokkos.cpp

to check the patch run cmd:
`diff pair_lj_cut_kokkos-buggy.cpp pair_lj_cut_kokkos-fixed.cpp`


