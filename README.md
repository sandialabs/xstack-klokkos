# X-Stack KLOKKOS: Automated Test Generation for Performance Portable Programs Using Clang/LLVM and Formal Methods
KLOKKOS is a portmanteau of Klee and Kokkos, is a project to develop automated test generation for performance-portable programs using Clang/LLVM and formal methods.

## Overview
Kokkos is a C++ software library to write portable, high-performance parallel code. However, software developed in Kokkos often has maintainability challenges, since there are subtle differences between architectures that may not appear in traditional testing, or cannot be tested (e.g., predicted behavior on future architectures).

The KLOKKOS project is meant to provide a suite of test generation and validation tools to help increase maintainability and portability of Kokkos programs. This is accomplished via several methods:
1. Design of a model of Kokkos code in the KLEE symbolic execution framework so that Kokkos code can be analyzed in an abstract way (that is, ignoring the implementation details of the many back-ends that Kokkos supports). This is henceforth referred to as the "Kokkos model" or "KLEE Kokkos model."
2. Code transformation tools to allow automated analysis using both KLEE or other static concolic analysis tools.
3. A formal specification to guide implementation of the KLOKKOS model.

Ultimately, this results in tools that can generate test cases for programs (that can indicate, e.g., subtle heterogeneity bugs or potentially data race bugs). Furthermore, these tools can be used to analyze existing Kokkos programs by indicating places where portability is not assured, through command-line based tools. This work can also help with documentation of Kokkos by adding many example programs, as well as specifications to consult to determine the correct behavior of a Kokkos program, even for architectures which have not yet been invented.

## Layout of this Repository 
This repository contains many different projects. As such there is not yet one unified way to perform test generation or modeling, however during this project we have developed several different approaches, outlined below.

### Kokkos Examples
It has been convenient for us to outline useful examples demonstrating the most common classes of mistakes Kokkos developers tend to make in order to test the analysis capabilities of our tools. These consist of
- mini apps: small but complete Kokkos problems solving an idealized, but still interesting problem.
- canonical mistakes: A small number of minimal working examples that have common mistakes Kokkos users make.
- other examples: a collection of kernels that identify key features of Kokkos.

### Formal Specification
This is a very early first draft towards a formal specification in Coq. The main work is continuing elsewhere, in preparation for publication and will likely be pen-and-paper in addition to some Coq formalization. Stay tuned!

### Klee plugin
The KL part of KLOKKOS, this is a start at developing a KLEE plugin to do symbolic execution of Kokkos programs.

### Mock Kokkos
Because KOKKOS is so complex, we use a "mock" back-end that provides a bare functionality to simplify analysis, while still providing the key API functionality.

### Kokkos Translator
Another approach to analyze Kokkos programs is to translate them into a simpler representation. This is implemented as a Clang tool.

## Publications
- F. Jin, J. Jacobson, S. D. Pollard and V. Sarkar, "MiniKokkos: A Calculus of Portable Parallelism," 2022 IEEE/ACM Sixth International Workshop on Software Correctness for HPC Applications (Correctness), Dallas, TX, USA, 2022, pp. 37-44, doi: [10.1109/Correctness56720.2022.00010](https://ieeexplore.ieee.org/document/10027583).

## Acknowledgments
This work is funded by the Department of Energy Advanced Scientific Computing Research (ASCR) X-Stack Programming Environments For Scientific Computing project (DE-FOA-0002460).

Sandia National Laboratories is a multimission laboratory managed and operated by National Technology and Engineering Solutions of Sandia, LLC., a wholly owned subsidiary of Honeywell International, Inc., for the U.S. Department of Energy’s National Nuclear Security Administration under contract DE-NA-0003525.

