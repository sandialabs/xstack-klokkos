#include <cstdio>
#include <Kokkos_Core.hpp>
//
// This is using functor
//

using view_type = Kokkos::View<double * [3]>;

struct InitView {
    view_type a;

    // Views have "view semantics."  This means that they behave like
    // pointers, not like std::vector.  Their copy constructor and
    // operator= only do shallow copies.  Thus, you can pass View
    // objects around by "value"; they won't do a deep copy unless you
    // explicitly ask for a deep copy.
    InitView(view_type a_) : a(a_) {}

    // Fill the View with some data.  The parallel_for loop will iterate
    // over the View's first dimension N.
    KOKKOS_INLINE_FUNCTION
    void operator()(const int i) const {
        // Acesss the View just like a Fortran array.  The layout depends
        // on the View's memory space, so don't rely on the View's
        // physical memory layout unless you know what you're doing.
        a(i, 0) = 1.0 * i;
        a(i, 1) = 1.0 * i * i;
        a(i, 2) = 1.0 * i * i * i;
    }
};

// Reduction functor that reads the View given to its constructor.
struct ReduceFunctor {
    view_type a;

    // Constructor takes View by "value"; this does a shallow copy.
    ReduceFunctor(view_type a_) : a(a_) {}

    // If you write a functor to do a reduction, you must specify the
    // type of the reduction result via a public 'value_type' alias.
    using value_type = double;

    KOKKOS_INLINE_FUNCTION
    void operator()(int i, double& lsum) const {
        lsum += a(i, 0) * a(i, 1) / (a(i, 2) + 0.1);
    }
};


int main(int argc, char* argv[]) {
    Kokkos::initialize(argc, argv);
    {
        const int N = 10;

        // Allocate the View.  The first dimension is a run-time parameter
        // N.  We set N = 10 here.  The second dimension is a compile-time
        // parameter, 3.  We don't specify it here because we already set it
        // by declaring the type of the View.
        //
        // Views get initialized to zero by default.  This happens in
        // parallel, using the View's memory space's default execution
        // space.  Parallel initialization ensures first-touch allocation.
        // There is a way to shut off default initialization.
        //
        // You may NOT allocate a View inside of a parallel_{for, reduce,
        // scan}.  Treat View allocation as a "thread collective."
        //
        // The string "A" is just the label; it only matters for debugging.
        // Different Views may have the same label.
        view_type a("A", N);

        // In Functor version, you have to explicitly select which Kokkos Views to be computed.
        Kokkos::parallel_for(N, InitView(a));
        double sum = 0;
        Kokkos::parallel_reduce(N, ReduceFunctor(a), sum);
        printf("Result: %f\n", sum);
    }  // use this scope to ensure the lifetime of "A" ends before finalize
    Kokkos::finalize();
}