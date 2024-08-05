#include <cstdlib>
#include <cmath>
#include <stdexcept>
#include <iostream>
#include <fstream>
#include <vector>
#include <limits>
#include <Kokkos_Core.hpp>
#include "MatrixComputationSerial.h"
#include "MatrixComputationCuda.h"
#include <boost/algorithm/string.hpp>

using namespace boost::algorithm;
using namespace std;

double L1_norm(const vector<double>& seq) {
    double sum = 0.0;
    for (double i : seq){
        sum += std::abs(i);
    }
    return (sum / seq.size());
}

double L2_norm(const vector<double>& seq){
    double sum = 0.0;
    for (double i : seq){
        sum += i*i;
    }
    return (sum / seq.size());
}

double Max_norm(const vector<double>& seq){
    double max = std::numeric_limits<double>::lowest();
    for (double i : seq){
        if (max < std::abs(i))
            max = std::abs(i);
    }
    return max;
}

bool compare(vector<double> colm_a, vector<double> colm_b, double tolerance=pow(10,-6), const string& norm="max"){
   if (colm_a.size() != colm_b.size() || colm_a.empty()|| colm_b.empty()){
        cout << "Cannot compare columns" << endl;
       return false;
    }
    vector<double> delta;
    for(int i=0; i < colm_a.size(); i++){
        delta.push_back(colm_a.at(i) - colm_b.at(i));
    }

    vector<int> not_same_rows;
    for(int i=0; i<delta.size(); i++){
        if(std::abs(delta.at(i)) > tolerance){
            not_same_rows.push_back(i);
        }
    }
    long num_same_rows = colm_a.size() - not_same_rows.size();
    double norm_err, norm_a, norm_b;

    if (norm == "L1") {
        norm_err = L1_norm(delta);
        norm_a = L1_norm(colm_a);
        norm_b = L1_norm(colm_b);
    }
    else if (norm == "L2") {
        norm_err = L2_norm(delta);
        norm_a = L2_norm(colm_a);
        norm_b = L2_norm(colm_b);
    }
    else if (norm == "max") {
        norm_err = Max_norm(delta);
        norm_a = Max_norm(colm_a);
        norm_b = Max_norm(colm_b);
    }
    else {
        throw std::invalid_argument("Invalid error norm");
    }
    if (norm_err < tolerance) {
        std::cout
                << "✅ norm_" << norm << "=" << norm_a << ", reference_norm_" << norm << "=" << norm_b << ", norm_err_"
                << norm << "=" << norm_err
                << endl;

        if (num_same_rows != colm_b.size()) {
            std::cout <<
                      "   WARNING: Only " << num_same_rows << " out of " << colm_b.size()
                      << " data points are identical"
                      << endl;
        }
        return true;
    }
    else{
        std::cout<<
        "❌ norm_" << norm << "=" << norm_a << ", reference_norm_" << norm << "=" << norm_b << ", norm_err_" << norm << "=" << norm_err << ">=" << tolerance << "!!!"
        << endl;
         return false;
    }
}

void getResultVectorsFromLog(const string& log_path, vector<double> &matrix_mul_result, vector<double> &dot_result, vector<double> &vector_y_before, vector<double> &vector_y_after){
    ifstream log(log_path);
    string log_line;
    bool mat_mul_result_flag = false;
    bool dot_result_flag = false;
    bool vector_y_before_flag = false;
    bool vector_y_after_flag = false;
    while (getline (log, log_line)) {
        if (log_line.find("Multiplication of given two matrices") != std::string::npos){
            mat_mul_result_flag = true;
            continue;
        }else if(log_line.find("value of vector y before dot operation is") != std::string::npos){
            mat_mul_result_flag = false;
            vector_y_before_flag = true;
            continue;
        }else if(log_line.find("value of vector y after dot operation is") != std::string::npos){
            mat_mul_result_flag = false;
            vector_y_before_flag = false;
            vector_y_after_flag = true;
            continue;
     	}else if(log_line.find("using Kokkos parallel constructs is") != std::string::npos){
            mat_mul_result_flag = false;
            vector_y_before_flag = false;
            vector_y_after_flag = false;
            dot_result_flag = true;
            continue;
      	}else if(log_line.find("using non-Kokkos C++ is") != std::string::npos){
            mat_mul_result_flag = false;
            vector_y_before_flag = false;
            vector_y_after_flag = false;
            dot_result_flag = false;
            continue;
        }

        if (mat_mul_result_flag){
            trim_left(log_line);
            trim_right(log_line);
    //        cout << " mat mul result: " << log_line << endl;
            matrix_mul_result.push_back(stod(log_line));
        }else if (vector_y_before_flag){
            trim_left(log_line);
            trim_right(log_line);
     //       cout << " vector y before: " << log_line << endl;
            vector_y_before.push_back(stod(log_line));
       }else if (vector_y_after_flag){
            trim_left(log_line);
            trim_right(log_line);
     //       cout << " vector y after: " << log_line << endl;
            vector_y_after.push_back(stod(log_line));
	}else if (dot_result_flag){
            trim_left(log_line);
            trim_right(log_line);
     //       cout << " dot result: " << log_line << endl;
            dot_result.push_back(stod(log_line));
        }
    }
    log.close();
}

bool compareLogs(const string& actual_log_path, const string& expected_log_path){

    vector<double> matrix_mul_result_actual;
    vector<double> matrix_mul_result_expected;
    vector<double> dot_result_actual;
    vector<double> dot_result_expected;
    vector<double> vector_y_before_actual;
    vector<double> vector_y_before_expected;
    vector<double> vector_y_after_actual;
    vector<double> vector_y_after_expected;

    getResultVectorsFromLog(actual_log_path, matrix_mul_result_actual, dot_result_actual, vector_y_before_actual, vector_y_after_actual);
    getResultVectorsFromLog(expected_log_path, matrix_mul_result_expected, dot_result_expected, vector_y_before_expected, vector_y_after_expected);
    if (matrix_mul_result_actual.empty() || dot_result_actual.empty() || matrix_mul_result_expected.empty() || dot_result_expected.empty()){
        cout << "results missing, abort process" << endl;
        return true;
    }else {
	
	bool return_value1 = false;     
	bool return_value2 = false;     
	bool return_value3 = false;     
	bool return_value4 = false;     
	cout << "comparing matrix multiplication results" << endl; 
        if (compare(matrix_mul_result_actual, matrix_mul_result_expected, pow(10, -6), "max") 
            //   && compare(matrix_mul_result_actual, matrix_mul_result_expected, pow(10,-6),"L1") 
            //   && compare(matrix_mul_result_actual, matrix_mul_result_expected, pow(10,-6),"L2") 
	   )
	{
		matrix_mul_result_actual.clear();
    		matrix_mul_result_expected.clear();
            	return_value1 = true;
	}
        else{
		matrix_mul_result_actual.clear();
    		matrix_mul_result_expected.clear();
            	return_value2 = false;
	}

	cout << "comparing vector y before" << endl; 
        if (compare(vector_y_before_actual, vector_y_before_expected, pow(10, -6), "max")
            //  && compare(vector_y_before_actual, vector_y_before_expected, pow(10,-6),"L1") 
            //  && compare(vector_y_before_actual, vector_y_before_expected, pow(10,-6),"L2")
	   )
	{
    		vector_y_before_actual.clear();
    		vector_y_before_expected.clear();
            	return_value2 = true;
	}
	else{
    		vector_y_before_actual.clear();
    		vector_y_before_expected.clear();
            	return_value2 = false;
	}
	
	cout << "comparing vector y after" << endl; 
        if (compare(vector_y_after_actual, vector_y_after_expected, pow(10, -6), "max")
            //  && compare(vector_y_after_actual, vector_y_after_expected, pow(10,-6),"L1") 
            //  && compare(vector_y_after_actual, vector_y_after_expected, pow(10,-6),"L2")
	   )
	{
    		vector_y_after_actual.clear();
    		vector_y_after_expected.clear();
            	return_value3 = true;
	}
	else{
    		vector_y_after_actual.clear();
    		vector_y_after_expected.clear();
            	return_value3 = false;
	}


	cout << "comparing dot product results" << endl; 
        if (compare(dot_result_actual, dot_result_expected, pow(10, -6), "max")
            //  && compare(dot_result_actual, dot_result_expected, pow(10,-6),"L1") 
            //  && compare(dot_result_actual, dot_result_expected, pow(10,-6),"L2")
	   )
	{
    		dot_result_actual.clear();
    		dot_result_expected.clear();
            	return_value4 = true;
	}
	else{
    		dot_result_actual.clear();
    		dot_result_expected.clear();
            	return_value4 = false;
	}
	return (return_value1 && return_value2 && return_value3 && return_value4);
    }
}

int main( int argc, char *argv[] )
{
    // invoke serial build and store result
    cout << "launching simulation using Serial back end" << endl;
    launchSerial(argc, argv);

    // invoke cuda build and compare result
    cout << "launching simulation using Cuda back end" << endl;
    launchCuda(argc, argv);

    Kokkos::finalize();

    string actual = "../cuda.log";
    string expected = "../serial.log";

    // if result match return 0 otherwise abort
    bool results_match = compareLogs(actual, expected);
    if (results_match){
        return 0;
    }else{
        abort();
    }
}
