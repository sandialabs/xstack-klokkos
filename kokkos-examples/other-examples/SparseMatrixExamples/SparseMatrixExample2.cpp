#include <iostream>
#include <fstream>
#include <Kokkos_Core.hpp>

namespace SpMat {
template<class ScalarType>
struct CSRMatrix
{
    int nRows;
    int nCols;
    int nNonz;
    Kokkos::View<int *> offset;
    Kokkos::View<int *> col_index;
    Kokkos::View<ScalarType *> values;
    Kokkos::View<int *>::HostMirror offset_host; // = Kokkos::create_mirror_view(A);
    Kokkos::View<int *>::HostMirror col_index_host;
    typename Kokkos::View<ScalarType *>::HostMirror  values_host;
    bool iniitalized;

public:
    CSRMatrix() {};

    CSRMatrix( int Rows, int Cols, int Nonz ) : nRows(0), nCols(0), nNonz(Nonz)
    {
        Kokkos::resize( offset, Rows+1 );
        Kokkos::resize( col_index, Nonz);
        Kokkos::resize( values, Nonz );
        offset_host = Kokkos::create_mirror_view(offset);
        col_index_host = Kokkos::create_mirror_view(col_index);
        values_host = Kokkos::create_mirror_view(values);
    };
    ~CSRMatrix(){};

    void setFromMatrixMarketFile( std::string &filename )
    {
        std::ifstream file(filename);
        if (!file)
        {
            std::cout << "Failed to open file\n";
            exit(1);
        }

        // Ignore comments headers
        while (file.peek() == '%') file.ignore(2048, '\n');

        // Read number of rows and columns
        file >> nRows >> nCols >> nNonz;
        // Change the size of Kokkos::View
        Kokkos::resize( offset, nRows);
        Kokkos::resize( col_index, nNonz );
        Kokkos::resize( values, nNonz);

        // Create Host Mirror
        offset_host = Kokkos::create_mirror_view(offset);
        col_index_host = Kokkos::create_mirror_view(col_index);
        values_host = Kokkos::create_mirror_view(values);

        // fill the matrix with data
        int prev_row = 1;
        int iRow = 0;
        offset_host[0] = 0;


        for (int i = 0; i < nNonz; ++i)
        {
            double data;
            int col, row;  // The file is sorted by column. We use row-based storage. So we swapped the index
            file >> col >> row >> data;

            col_index_host[i] =  col-1; // Adjust to C/C++ indexing
            values_host[i] = data;
            if( prev_row != row ) {
                iRow++;
                offset_host[iRow] = i;
                prev_row=row;
            }
        }

        offset_host[nRows] = nNonz;
        // Copy data from host to the device.
        // For CPU-only platforms, it does nothing. HostMirror points the original Kokkos::View
        Kokkos::deep_copy(offset,offset_host);
        Kokkos::deep_copy(col_index,col_index_host);
        Kokkos::deep_copy(values,values_host);
        file.close();
    }

    void set2DStencil( int n ) // This creates a sparse matrix from 2D (nxn) regular mesh
    {
        nRows = n*n;
        nCols = n*n;
        nNonz = 5*n*n - (2*4) - ((n-2)*4);  // Corner and edge
        Kokkos::resize( offset, nRows+1);
        Kokkos::resize( col_index, nNonz );
        Kokkos::resize( values, nNonz);

        // Create Host Mirror
        offset_host = Kokkos::create_mirror_view(offset);
        col_index_host = Kokkos::create_mirror_view(col_index);
        values_host = Kokkos::create_mirror_view(values);

        // Assign the data to the host
        int iNonz = 0;
        int iRow = 0;
        offset_host(iRow) = 0;
        for ( int i=0; i < n; ++i )
        {
            for ( int j = 0; j < n; ++j )
            {
                int nonz_row=0;
                // Check node on the bottom
                if( i > 0 ) {
                    col_index_host(iNonz) = iRow - n;
		    printf("col_index %d\n",col_index_host(iNonz) );
                    values_host(iNonz) = -1.0;
                    iNonz++;
                    nonz_row++;
                }
                // Check node on the left
                if( j > 0 ) {
                    col_index_host(iNonz) = iRow - 1;
		    printf("col_index %d\n",col_index_host(iNonz) );
                    values_host(iNonz) = -1.0;
                    iNonz++;
                    nonz_row++;
                }
                // My node
                col_index_host(iNonz) = iRow;
		    printf("col_index %d\n",col_index_host(iNonz) );
                values_host(iNonz) = 4;
                iNonz++;
                nonz_row++;

                // Check node on the right
                if( j < n-1 ) {
                    col_index_host(iNonz) = iRow +1;
		    printf("col_index %d\n",col_index_host(iNonz) );
                    values_host(iNonz) = -1;
                    iNonz++;
                    nonz_row++;
                }

                // Check node on top
                if( i < n-1 ) {
                    col_index_host(iNonz) = iRow + n;
		    printf("col_index %d\n",col_index_host(iNonz) );
                    values_host(iNonz) = -1;
                    iNonz++;
                    nonz_row++;
                }

                offset_host(iRow+1) = offset_host(iRow) + nonz_row;
	        printf("offset  %d %d\n",offset_host(iRow+1),offset_host(iRow));
                iRow++ ;
            }
        }
	printf("iNonz %d %d, iRow %d\n",iNonz,nNonz,iRow);
        // Copy data from host to the device.
        // For CPU-only platforms, it does nothing. HostMirror points the original Kokkos::View
	std::cout <<"Done with matrix generation\n";
        Kokkos::deep_copy(offset,offset_host);
        Kokkos::deep_copy(col_index,col_index_host);
        Kokkos::deep_copy(values,values_host);
    }

    // We need unit test for these methods
    void setNumRows(int n)
    {
        nRows = n;
        Kokkos::resize( offset, n+1 ); // Offset size is always (# of rows)+1
    }

    void setNumCols(int n) { nRows = n; }

    void setNumNonz(int n) {
        nNonz = n;
        Kokkos::resize(col_index,n);
        Kokkos::resize(values,n);
    }

    int getNumRows( ) { return nRows; }
    int getNumCols( ) { return nCols;}
    int getNumNonz( ) { return nNonz;}

};


void SpMV( const int nRows, const int nCols, const Kokkos::View<int *> &offset, const Kokkos::View<int *> &col_index, const Kokkos::View<double  *> &values, const Kokkos::View<double  *> &X, Kokkos::View<double  *> &Y )
{
     if (X.extent(0) !=  nRows )
     {
         std::cout << "Size Mismatch between Matrix " << nRows << " and Vector X " << X.extent(0) << std::endl;
         return;
     }

     if (Y.extent(0) !=  nCols )
     {
         std::cout << "Size Mismatch between Matrix " << nRows << " and Vector Y " << Y.extent(0) << std::endl;
         return;
     }


     // This is not efficient for GPUs because no nested parallelism is used
     Kokkos::parallel_for( nRows, KOKKOS_LAMBDA(const int i)
     {
         double row_sum = 0;
         for( int j = offset(i) ; j < offset(i+1); ++j )
         {
            row_sum += values(j) * X(col_index(j));
         }
         Y(i) = row_sum; // No race
     });
     Kokkos::fence();
     return;
}

}

int main( int argc, char *argv[] )
{

    Kokkos::initialize(argc,argv);
    std::string fileName;

    std::string current_exec_name = argv[0]; // Name of the current exec program
    if (argc > 1 ) {
        fileName = argv[1];
    } else {
        fileName  = "../bcsstk11.mtx";
    }

    {
        // Read data for A, x and b
	SpMat::CSRMatrix<double> A;
        Kokkos::View<double *> x;
        Kokkos::View<double *> b;

        A.setFromMatrixMarketFile(fileName);
        std::cout << "Reading a matrix" << fileName << " " << std::endl;
        std::cout << A.getNumRows() << " rows," << A.getNumNonz() <<
        " nonzero entries" << std::endl;

        Kokkos::resize(x,A.getNumCols());
        Kokkos::resize( b, A.getNumRows());
        auto b_host= Kokkos::create_mirror_view(b);
        Kokkos::deep_copy(x,1.0); // Set all values to be 1.0
        Kokkos::deep_copy(b, 0.0); // Set all values to be 0.0
        Kokkos::deep_copy(b_host, 0.0); // Set all values to be 0.0
        // b = b + A*x
        SpMat::SpMV(A.nRows,A.nCols,A.offset,A.col_index,A.values,x,b);
        Kokkos::deep_copy(b_host,b);
        for( int i = 0; i < A.nCols; ++i ){
           std::cout << "b( " << i << " ) " << b_host(i) <<  std::endl;
        }
        std::cout << "Done with Sparse MatVec\n";


    }
    Kokkos::finalize();
    return 0;
}

