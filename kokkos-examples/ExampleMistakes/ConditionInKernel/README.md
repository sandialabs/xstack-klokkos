### APPLICATION:
We use a small kokkos-based application called MatrixComputation that is designed to be executed using Kokkos's Serial and Cuda back ends. 
The application implements the source code to compute the following formula:  
			
`DOT(MUL(A, x),y)` 

where, `MUL(A,y)` is a method to perform multiplication of a matrix `A` with a vector `x` and `DOT(x, y)` is a method to perform dot product of two vectors `x` and `y`.

The input to the application are two integers that correspond to the two dimensions of matrix `A`: `nRows` and `nCols`, which are read from the file. 

#### IMPLEMENTATION LOGIC:
- The application initializes a matrix `A(nRows, nCols)`, a vector `x(nCols)`, and a vector `y(nRows)` with values in range [1, 100000] sampled uniformly randomly.  
- Next, the application computes `result = MUL(A, x)` and logs the multiplication result to a file.
- Finally, the application computes `DOT(result, y)` and logs the final result (scalar value) to a file. 

### BUG INFORMATION:
We seed two bugs in the application:
1. *Out of bound bug*: In the `parallel_for` of the `MUL` method: This bug occurs when the input dimensions are large (~2000) and the Cuda version crashes as the index of the matrix being accessed can be greater than the total number of rows in the matrix `A`.
2. *Data race bug*: In the `parallel_reduce` of the `DOT` method:  This bug occurs when `y` vector's element at an index `i+1` is updated using it's value from the index `i` when `i==7`. 

### OUTPUT LOG INFORMATION:
The application outputs two log files (`serial.log` and `cuda.log`) that contain the following information:
1. number of dimensions 
2. result of `MUL(A,y)`
3. vector `y` values before performing `DOT` operation  
4. vector `y` values aftyer performing `DOT` operation
5. final result computed using kokkos constructs 
6. final result computed using non-kokkos constructs   

### DRIVER PROGRAM:
We develop a driver program that launches the two versions of the application and compares the generated logs.
Unlike traditional systems, scientific simulations allow the outputs to vary as long as they are within a specified error margin. 
The driver program implements these error margins (L1 norm, L2 norm, and max norm) and reports if the difference between the outputs 
of the two versions are greater than the specified tolerance. 

### HOW TO RUN:
Install Kokkos version 3.7 and enable Serial, OpenMP, and Cuda backends. Run the following commands within this dir. 
1. `mkdir build`
2. `cd build`
3. `cmake ..`  (if successfull, it will generate `Driver` executable)
4. `./Driver ../input.txt`   (`input.txt` contains two integers, nRows and nCols. You can modify these values to test the application with different inputs.)

### OUTPUT:
The output is printed on the console (results that match and results that differ). 
The output log files `serial.log` and `cuda.log` contain the raw results. 

### FINDING:
For the current example, the `if statement` in the `parallel_reduce` of the `DOT` method makes the cuda version of the program executed serially (due to how cuda handles if inside parallel constructs) and for the serial version, we observe wrong output due to data race error. This was an accidental finding as the goal of developing this example was to introduce a race condition that will result in wrong output when the application is run using cuda and correct output when run on serial. However, in this example, we observe the opposite of what was intended, i.e., correct output in cuda and wrong in serial. 
