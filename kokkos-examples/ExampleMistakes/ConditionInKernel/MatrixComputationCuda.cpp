#include <cstdio>
#include <cstdlib>
#include <random>
#include <typeinfo>
#include <Kokkos_Core.hpp>
#include <Kokkos_Random.hpp>
#include <boost/algorithm/string.hpp>
#include <iostream>
#include <fstream>
#include "MatrixComputationCuda.h"

using namespace boost::algorithm;
using namespace std;

#ifndef EXE_SPACE
#define EXE_SPACE Cuda
#endif

// multiply two matrices A.X

Kokkos::View<double *,Kokkos::EXE_SPACE::memory_space> computeMatrixMulCuda(Kokkos::View<double **,Kokkos::EXE_SPACE::memory_space> A_d, Kokkos::View<double *,Kokkos::EXE_SPACE::memory_space> B_d, int nRows, int nCols)
{
	Kokkos::View<double *,Kokkos::EXE_SPACE::memory_space> tmp_d("Vec_TMP",nRows);
	auto tmp_h = Kokkos::create_mirror_view(tmp_d);
	Kokkos::Profiling::pushRegion("First Parallel For And Reduce");
	typedef Kokkos::TeamPolicy<Kokkos::EXE_SPACE> Policy;
	Policy policy(nRows,Kokkos::AUTO); // Using pre-set value for league, team partitions
	Kokkos::parallel_for (policy, KOKKOS_LAMBDA (Policy::member_type team)
			{
			const auto iRow = team.team_size() * team.league_rank() + team.team_rank();
			// Without the if statement, the GPU code may fail or produce incorrect output as iRow can be greater than nRows
#ifndef WITH_BUG
						     if( iRow >= nRows ) return;
#endif
			tmp_d(iRow) = 0;
			Kokkos::parallel_reduce (Kokkos::ThreadVectorRange(team, nCols), [&] (int &iCol, double &local_x)
					{
					local_x += A_d(iRow,iCol) * B_d(iCol) ;
					}, tmp_d(iRow));
			});

	Kokkos::Profiling::popRegion();

#ifndef WITH_BUG
	Kokkos::deep_copy(tmp_h,tmp_d);
#endif

 	ofstream outdata;
	outdata.open("../cuda.log", std::ios_base::app);
        if( !outdata ) { // file couldn't be opened
                cerr << "Error: file could not be opened" << endl;
                exit(1);
        }
	outdata << "Multiplication of given two matrices ("<< nRows << "x" << nCols << ").(" << nCols << "x1)" << " using kokkos constructs is:" << endl;
	for (int i = 0; i < nRows; i++) {
		outdata << tmp_h(i) << std::endl;
	}
	outdata.close();
	return tmp_d;
}


void mulMatCuda(Kokkos::View<double **, Kokkos::Cuda::array_layout, Kokkos::Device<Kokkos::HostSpace::execution_space, Kokkos::HostSpace::memory_space>> A_h, Kokkos::View<double *, Kokkos::Cuda::array_layout, Kokkos::Device<Kokkos::HostSpace::execution_space, Kokkos::HostSpace::memory_space>> B_h, int nRows, int nCols)
{
    ofstream outdata;
    outdata.open("../cuda.log", std::ios_base::app);
    if( !outdata ) { // file couldn't be opened
        cerr << "Error: file could not be opened" << endl;
        exit(1);
    }

    Kokkos::View<double **, Kokkos::Cuda::array_layout, Kokkos::Device<Kokkos::HostSpace::execution_space, Kokkos::HostSpace::memory_space>> rslt("MAT_A_times_B",nRows,1);
    outdata << "Multiplication of given two matrices ("<< nRows << "x" << nCols << ").(" << nCols << "x1)" << " without using kokkos constructs is:" << endl;
    for (int i = 0; i < nRows; i++) {
        for (int j = 0; j < 1; j++) {
	    rslt(i,j) = 0.0;
            for (int k = 0; k < nCols; k++) {
                rslt(i,j) += A_h(i,k) * B_h(k);
            }
            outdata << rslt(i,j) << "\t";
        }
 	outdata << std::endl;
    }
    outdata.close();
}


// compute Dot product SUM(A[i]*B[i])
void computeDotCuda(Kokkos::View<double *,Kokkos::EXE_SPACE::memory_space> A_h, Kokkos::View<double *,Kokkos::EXE_SPACE::memory_space> B_h, int nRows)
{
	auto A_d = Kokkos::create_mirror_view(A_h);
	auto B_d = Kokkos::create_mirror_view(B_h);
	
 	ofstream outdata;
	outdata.open("../cuda.log", std::ios_base::app);
        if( !outdata ) { // file couldn't be opened
                cerr << "Error: file could not be opened" << endl;
                exit(1);
        }

	Kokkos::deep_copy(B_d,B_h);
	outdata << "value of vector y before dot operation is:" << std::endl;
        for ( int iRow = 0; iRow < nRows; ++iRow){
            outdata<< B_d(iRow) << "\n";
        }

	double result = 0;
	Kokkos::Profiling::pushRegion("Parallel Reduce2");
	Kokkos::parallel_reduce( Kokkos::RangePolicy<Kokkos::EXE_SPACE>(0,nRows),
		KOKKOS_LAMBDA(const size_t &iRow, double & valueToUpdate )
		{
		     #ifndef WITH_BUG
			if (iRow == 7){
				B_h((iRow+1)%nRows) = B_h(iRow)-1;  // race condition because we do not know when B(iRow) is updated
			}
		    #endif
			valueToUpdate += A_h(iRow) * B_h(iRow) ;
		}
	,result);

	auto B_d_updated = Kokkos::create_mirror_view(B_h);
	Kokkos::deep_copy(B_d_updated,B_h);
	Kokkos::deep_copy(A_d,A_h);
	outdata << "value of vector y after dot operation is:" << std::endl;
    for ( int iRow = 0; iRow < nRows; ++iRow){
       	outdata<< B_d_updated(iRow) << "\n";
    }
    outdata << "Dot product of resultant matrix (" << nRows << "x1) with a vector (" << nRows << "x1)" <<  " using Kokkos parallel constructs is:\n" <<  std::scientific << result << std::endl;
	double res = 0;
	for ( int iRow = 0; iRow < nRows; ++iRow){
		res += A_d(iRow ) * B_d(iRow);
	}
    outdata << "Dot product of resultant matrix (" << nRows << "x1) with a vector (" << nRows << "x1)" <<  " using non-Kokkos C++ is:\n" <<  std::scientific << res << std::endl;
	outdata.close();

}


void initializeViewsCuda(Kokkos::View<double **, Kokkos::Cuda::array_layout, Kokkos::Device<Kokkos::HostSpace::execution_space, Kokkos::HostSpace::memory_space>> A_h, Kokkos::View<double *, Kokkos::Cuda::array_layout, Kokkos::Device<Kokkos::HostSpace::execution_space, Kokkos::HostSpace::memory_space>> x_h, Kokkos::View<double *, Kokkos::Cuda::array_layout, Kokkos::Device<Kokkos::HostSpace::execution_space, Kokkos::HostSpace::memory_space>> y_h, int nRows, int nCols, double lower_bound, double upper_bound){
	
	std::uniform_real_distribution<double> unif(lower_bound,upper_bound);
	std::default_random_engine re;
	for ( int iRow = 0; iRow < nRows; ++iRow)
	{
		y_h(iRow) = unif(re); // 1.0
		for ( int iCol = 0; iCol < nCols; ++iCol )
		{
			A_h(iRow,iCol) = unif(re); // 1.0
			x_h(iCol) = unif(re); // 1.0
					 //	 std::cout<< "A[i,j]:" << " i=" << iRow << " j=" << iCol<< " A[i,j]=" << A_m(iRow,iCol) << std::endl;
					 //	 std::cout<< "i=" << iRow<< " y[i]=" << y_m(iRow) << std::endl;
					 //	 std::cout<< "j=" << iCol<< " x[j]=" << x_m(iCol) << std::endl;
		}
	}
}


bool isASCIICuda(const std::string& s)
{
    return !std::any_of(s.begin(), s.end(), [](char c) {
        return static_cast<unsigned char>(c) > 127;
    });
}

bool is_numberCuda(const std::string& s)
{
    return !s.empty() && std::find_if(s.begin(),
        s.end(), [](unsigned char c) { return !std::isdigit(c); }) == s.end();
}

// Dot(Mul(A,x),y)  A(2,5) x(5,1)=> (2,1) y(2,1) => scalar 

int launchCuda( int argc, char *argv[] )
{
	double lower_bound = 1.0;
	double upper_bound = 100.0;
	int nRows = 2;
	int nCols = 4;
 	ofstream outdata;
	outdata.open("../cuda.log");
	if( !outdata ) { // file couldn't be opened
		cerr << "Error: file could not be opened" << endl;
		exit(1);
	}

	outdata << "reading dimensions from file: " << argv[1] << argc << endl;

    std::ifstream inputfile (argv[1], std::ifstream::in);
	std::string inputstring;

	if (inputfile.is_open() ) {
		ostringstream ss;
      		ss << inputfile.rdbuf(); // reading data
      		inputstring = ss.str();
		outdata << "input string:" << inputstring << std::endl;
		if (!isASCIICuda(inputstring)){
			outdata.close();
			return 1;
		}
		trim_left(inputstring);
		trim_right(inputstring);
	}

	// Vector of string to save tokens
    	vector <string> tokens;

    	// string stream class check1
    	stringstream check1(inputstring);

    	string intermediate;

    	// Tokenizing w.r.t. space ' '
    	while(getline(check1, intermediate, ' '))
    	{
		if (!is_numberCuda(intermediate)){
			outdata.close();
                        return 1;
                }
        	tokens.push_back(intermediate);
    	}

	outdata << "number of dimensions:" << tokens.size() << std::endl;

	if (tokens.size() < 2){
		outdata.close();
		return 1;
	}


	std::string n_rows = tokens[0];
	std::string n_cols = tokens[1];

	trim_left(n_rows);
	trim_right(n_rows);
	trim_left(n_cols);
	trim_right(n_cols);

	outdata << "n_rows: " << n_rows << std::endl;
	outdata << "n_cols: " << n_cols << std::endl;

	if (argc >= 2) {
		try {
			nRows = stoi(n_rows);
			nCols = stoi(n_cols);
  		}
  		catch (const std::out_of_range& oor) {
    			outdata << "Out of Range error: " << oor.what() << '\n';
			outdata.close();
			return 1;
  		}
	}

	if (nRows > 10000 || nCols > 10000){
    		outdata << "Out of Range error\n";
		outdata.close();
		return 1;
	}

 //	Kokkos::initialize(argc, argv);
//	{
		Kokkos::View<double **, Kokkos::EXE_SPACE::memory_space> A_h("MAT_A",nRows,nCols);
		Kokkos::View<double *, Kokkos::EXE_SPACE::memory_space> x_h("Vec_X",nCols);
		Kokkos::View<double *,Kokkos::EXE_SPACE::memory_space> tmp_h("Vec_TMP",nRows);
		Kokkos::View<double *, Kokkos::EXE_SPACE::memory_space> y_h("Vec_Y",nRows);
		auto A_d = Kokkos::create_mirror_view(A_h);
		auto x_d = Kokkos::create_mirror_view(x_h);
		auto y_d = Kokkos::create_mirror_view(y_h);
		initializeViewsCuda(A_d, x_d, y_d, nRows, nCols, lower_bound, upper_bound);
		Kokkos::deep_copy(A_h, A_d);
		Kokkos::deep_copy(x_h, x_d);
		Kokkos::deep_copy(y_h, y_d);

	/*
	for ( int iRow = 0; iRow < nRows; ++iRow)
	{
		for ( int iCol = 0; iCol < nCols; ++iCol )
		{
			 std::cout<< "A_d[i,j]:" << " i=" << iRow << " j=" << iCol<< " A_d[i,j]=" << A_d(iRow,iCol) << std::endl;
		}
	}
	*/
//	mulMat(A_d, x_d, nRows, nCols);
	tmp_h = computeMatrixMulCuda(A_h, x_h, nRows, nCols);
	computeDotCuda(tmp_h, y_h, nRows);
//	}
//	Kokkos::finalize();

	outdata.close();
	return 0;
}

/*
int main( int argc, char *argv[] ){
        return launchCuda(argc, argv);
}*/
