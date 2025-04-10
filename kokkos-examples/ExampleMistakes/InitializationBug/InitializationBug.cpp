#include <cstdio>
#include <cstdlib>
#include <Kokkos_Core.hpp>
//
// This Program includes a mistake of Kokkos::deep_copy where the size does not match
//

struct mydata {
#ifdef WITH_BUG
    KOKKOS_INLINE_FUNCTION mydata() = default;
#else
    KOKKOS_INLINE_FUNCTION mydata(): x(0), y(0) {}; // This must be KOKKOS_INLINE_FUNCTION
#endif
    KOKKOS_INLINE_FUNCTION mydata( int xin , double yin) : x(xin), y(yin) {};
    KOKKOS_INLINE_FUNCTION mydata( int xin ) : x(xin), y(0) {};
    KOKKOS_INLINE_FUNCTION mydata( double yin) : x(0), y(yin) {};
    KOKKOS_INLINE_FUNCTION ~mydata() {};

    KOKKOS_INLINE_FUNCTION
    mydata operator+ (const mydata &in)
    {
        mydata out;
        out.x = this->x  + in.x;
        out.y = this->y + in.y;
        return out;
    }

    KOKKOS_INLINE_FUNCTION
    mydata & operator+= (const mydata &in)
    {
        this->x += in.x;
        this->y += in.y;
        return *this;
    }

    int x;
    double y;
};

int main( int argc, char *argv[] )
{
    Kokkos::initialize(argc,argv);
    {
        int mysize;
        if (argc == 2 )
        {
            mysize = std::atoi(argv[1]);
        } else 
        {
            mysize = 10;
        } 
        {
            Kokkos::View<double *> A("A",2*mysize); // Allocated in the Default Memory Space
            Kokkos::deep_copy(A,12.32);
            double out;
            Kokkos::parallel_reduce(mysize*2, KOKKOS_LAMBDA(const size_t index, double &local ) {
                local += A(index);
            },out);
            std::cout << "Test run " << out << std::endl;
        }
        {
        Kokkos::View<mydata *> A("A", mysize); // Allocated in the Default Memory Space
        mydata out;
        Kokkos::parallel_reduce(mysize, KOKKOS_LAMBDA(const size_t index, mydata &local ) {
            local += A(index);
        },out);
        // The user wants to get 0
        std::cout << "X is " << out.x << " and Y is " << out.y << " for View of struct with the length of " << mysize << std::endl;
        }
    }
    Kokkos::finalize();
    return 0;
}
