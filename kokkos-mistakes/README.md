# Canonical Mistakes

The canonical mistakes contained here exemplify the 4 categories of programming errors initially targeted by klokkos.

* example1.cpp: Copy between incompatible views (e.g., different size, layout)
* example2.cpp: Intra-kernel race condition (e.g., potential conflicting accesses by iterations of a parallel_for)
* example3.cpp: Heterogeneous memory error (e.g., accessing device memory from host)
* example4.cpp: Missing fence (between kernels dispatched async in multiple exec spaces)

When compiled defining `WITH_BUG`, each example program exhibits the corresponding defect.
Without the `WITH_BUG` definition, the example program is a correctly functioning `Kokkos` program.
Each of these examples should be minimal, in that they should only contain sufficient `Kokkos` functionality as to demonstrate the cooresponding defect classification.

