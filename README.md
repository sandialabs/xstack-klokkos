# X-Stack KLOKKOS: Automated Test Generation for Performance Portable Programs Using Clang/LLVM and Formal Methods
KLOKKOS, a portmanteau of Klee and Kokkos, is a project to develop automated test generation for performance-portable programs - specifically Kokkos parallel programs - using Clang/LLVM and formal methods. 


## Overview
Kokkos is a C++ software library to write portable, high-performance parallel code. However, software developed in Kokkos often has maintainability challenges, since there are subtle differences between architectures that may not appear in traditional testing, or cannot be tested (e.g., predicted behavior on future architectures).

The KLOKKOS project is meant to provide a suite of test generation and validation tools to help increase maintainability and portability of Kokkos programs. This is accomplished via several methods:
1. Design of a model of Kokkos code in the KLEE symbolic execution framework so that Kokkos code can be analyzed in an abstract way (that is, ignoring the implementation details of the many back-ends that Kokkos supports). This is henceforth referred to as the "Kokkos model" or "KLEE Kokkos model."
2. Code transformation tools to allow automated analysis using both KLEE or other static concolic analysis tools.
3. A formal specification to guide implementation of the KLOKKOS model.

Ultimately, this results in tools that can generate test cases for programs (that can indicate, e.g., subtle heterogeneity bugs or potentially data race bugs). Furthermore, these tools can be used to analyze existing Kokkos programs by indicating places where portability is not assured, through command-line based tools. This work can also help with documentation of Kokkos by adding many example programs, as well as specifications to consult to determine the correct behavior of a Kokkos program, even for architectures which have not yet been invented.


## Integration with Kokkos Ecosystem 
Though KLOKKOS has been a research project for X-stack project from ASCR post-ECP, Kokkos is geared toward being production software for Kokkos developers. The development of Klokkos is aimed at being part of the 'HPC Tools for Kokkos' subecosystem of the Kokkos ecosystem. [Kokkos-Tools](https://link.springer.com/chapter/10.1007/978-3-030-02465-9_53) is one github repository within this subecosystem, and this repository contains dynamic program analysis debugging tools using the Kokkos Tools infrastructure, specifically kernel-logger and memory-events. Yet, these debugging tools need to be complemented with static program analysis tools, especially when the architecture is not available. There are two static analysis tools for Kokkos parallel programming that have proved beneficial: analysis of the Abstract Syntax Tree (AST) representation of a Kokkos program (a clang-tidy fork to support Kokkos library functions, i.e., Kokkos-clang-tidy) and the use symbolic execution of the Intermediate Representation (IR) of a Kokkos parallel program (Klee extension for Kokkos, i.e., Klokkos). We assume clang/LLVM's AST and IR for both tools, but the approach can be replicated to other compilers, e.g., GCC. 

## Layout of this Repository 
This repository contains many different projects. As such there is not yet one unified way to perform test generation or modeling, however during this project we have developed several different approaches, outlined below. 

### Kokkos Examples
It has been convenient for us to outline useful examples demonstrating the most common classes of mistakes Kokkos developers tend to make in order to test the analysis capabilities of our tools. These consist of a collection of kernels that identify key features of Kokkos.
These are common computations in real-world Kokkos applications that are bug-prone.

### Kokkos Mistakes
These consist of a canonical set of examples of typical portability mistakes encountered in a survey of the Kokkos examples above. There are 7 different examples. Though each of these are important, we highlight heterogeneous memory data races because they are fundamental and challenging in parallel computing. 

### KLEE-2.3
Source code snapshot of our modified (forked) KLEE version 2.3.

### Mock Kokkos
Because KOKKOS is so complex, we use a "mock" backend (of Kokkos0 that provides a bare functionality to simplify analysis, while still providing the key API functionality.

### Formal Specification
This is a very early first draft towards a formal specification in Coq. The main work is continuing elsewhere, in preparation for publication and will likely be pen-and-paper in addition to some Coq formalization. Stay tuned!

### Klee plugin
The KL part of KLOKKOS, this is a start at developing a KLEE plugin to do symbolic execution of Kokkos programs.

### Kokkos Translator
Another approach to analyze Kokkos programs is to translate them into a simpler representation. This is implemented as a Clang tool.

## Publications
- F. Jin, J. Jacobson, S. D. Pollard and V. Sarkar, "MiniKokkos: A Calculus of Portable Parallelism," 2022 IEEE/ACM Sixth International Workshop on Software Correctness for HPC Applications (Correctness), Dallas, TX, USA, 2022, pp. 37-44, doi: [10.1109/Correctness56720.2022.00010](https://ieeexplore.ieee.org/document/10027583).
- V. Kale, H. Yu, S. Mukherjee, K. Teranishi, J. Mayo, A. Orso and R. Rutledge. Automated Debugging for Kokkos Parallel Programs. 2024 IEEE/ACM Sixth International Workshop on Software Correctness for HPC Applications (Correctness), Denver, CO, USA, 2024. https://dl.acm.org/doi/pdf/10.1109/SCW63240.2024.00029

## Acknowledgments
This work is funded by the Department of Energy Advanced Scientific Computing Research (ASCR) X-Stack Programming Environments For Scientific Computing project (DE-FOA-0002460). 

Sandia National Laboratories is a multimission laboratory managed and operated by National Technology and Engineering Solutions of Sandia, LLC., a wholly owned subsidiary of Honeywell International, Inc., for the U.S. Department of Energy’s National Nuclear Security Administration under contract DE-NA-0003525.
