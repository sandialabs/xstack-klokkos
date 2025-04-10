#include <cstdio>
#include <iostream>
#include <cstdlib>
#include <vector>

template<class ScalarType>
class Spmat
{
    int nRows;
    int nCols;
    int nNonz;
    std::vector<int> offset;
    std::vector<int> col_index;
    std::vector<ScalarType> values;
    // No Heterogeneous computing capability (Should we write CUDA/SYCL/HIP versions?
    bool iniitalized;

public:
#if 1
    Spmat() {};

    Spmat( int Rows, int Cols, int Nonz ) : nRows(0), nCols(0), nNonz(Nonz)
    {
        offset.resize(  Rows+1 );
        col_index.resize( Nonz);
        values.resize( Nonz );
        // No heterogeneous part
    };
    ~Spmat(){};
#endif

#if 0
    // Opens a file and create a sparse matrix in the host space and copy to the original Kokkos::View if needed
    void setFromFile( std::string fname )
    {


        // Copy data from host to the device.
        // For CPU-only platforms, it does nothing. HostMirror points the original Kokkos::View
        Kokkos:deep_copy(offset,offset_host);
        Kokkos:deep_copy(col_index,col_index_host);
        Kokkos:deep_copy(values,values_host);
    }
#endif

    void set2DStencil( int n ) // This creates a sparse matrix from 2D (nxn) regular mesh
    {
        nRows = n*n;
        nCols = n*n;
        nNonz = 5*n*n - (2*4) - ((n-2)*4);  // Corner and edge
        offset.resize(n*n+1);
        col_index.resize(nNonz);
        values.resize(nNonz);


        // Assign the data to the host
        int iNonz = 0;
        int iRow = 0;
        offset[iRow] = 0;
        for ( int i=0; i < n; ++i )
        {
            for ( int j = 0; j < n; ++j )
            {
                int nonz_row=0;
                // Check node on the bottom
                if( i > 0 ) {
                    col_index[iNonz] = iRow - n;
                    values[iNonz] = -1.0;
                    iNonz++;
                    nonz_row++;
                }
                // Check node on the left
                if( j > 0 ) {
                    col_index[iNonz] = iRow - 1;
                    values[iNonz] = -1.0;
                    iNonz++;
                    nonz_row++;
                }
                // My node
                col_index[iNonz] = iRow;
                values[iNonz] = 4;
                iNonz++;
                nonz_row++;

                // Check node on the right
                if( j < n-1 ) {
                    col_index[iNonz] = iRow +1;
                    values[iNonz] = -1;
                    iNonz++;
                    nonz_row++;
                }

                // Check node on top
                if( i < n-1 ) {
                    col_index[iNonz] = iRow + n;
                    values[iNonz] = -1;
                    iNonz++;
                    nonz_row++;
                }

                offset[iRow+1] = offset[iRow] + nonz_row;
                iRow++ ;
            }
        }

    }

    // We need unit test for these methods
    void setNumRows(int n)
    {
        nRows = n;
        offset.resize( n+1 ); // Offset size is always (# of rows)+1
    }

    void setNumCols(int n) { nRows = n; }

    void setNumNonz(int n) {
        nNonz = n;
        col_index.resize(n);
        values.resize(n);
    }

    int getNumRows( ) { return nRows; }
    int getNumCols( ) { return nCols;}
    int getNumNonz( ) { return nNonz;}

    void apply( const std::vector<ScalarType> &X, std::vector<ScalarType> &Y )
    {
        if (X.size() !=  nRows )
        {
            std::cout << "Size Mismatch between Matrix " << nRows << " and Vector X " << X.size() << std::endl;
            return;
        }

        if (Y.size() !=  nCols )
        {
            std::cout << "Size Mismatch between Matrix " << nRows << " and Vector Y " << Y.size() << std::endl;
            return;
        }


        // This is not efficient for GPUs because no nested parallelism is exploited
        for( int i = 0; i < nRows; ++i)
        {
            double row_sum = 0;
            // std::cout << " offset (" << i << ") = " << offset(i) << std::endl;

            for( int j = offset[i] ; j < offset[i+1]; ++j )
            {

                row_sum += values[j] * X[col_index[j]];
            }
            Y[i] += row_sum; // No race
            std::cout << "Y(" << i << ") = " << Y[i] <<std::endl;
        }
    }
};


int main( int argc, char *argv[] )
{

    int meshSize = 10;
    int M = meshSize*meshSize;
    int N = meshSize*meshSize;

    // Read data for A, x and b
    Spmat<double> A;
    std::vector<double > x;
    std::vector<double > b;

    A.set2DStencil(meshSize);
    x.resize(N);
    b.resize(M);
    for( int i = 0; i < M; ++i ) x[i]=1.0;
    for( int i = 0; i < M; ++i ) b[i]=0.0;
    // b = b + A*x
    A.apply(x,b);

    return 0;
}
