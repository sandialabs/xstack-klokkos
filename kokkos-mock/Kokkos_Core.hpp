
#include <cstddef>
#include <cstdint>
#include <string>
#include <klee/klokkos.h>

#define KOKKOS_LAMBDA [&]

namespace Kokkos
{

uint32_t AUTO = 0;

template<typename UNUSED = char> struct RangePolicy {
  int32_t begin;
  int32_t end;
  RangePolicy(int32_t b, int32_t e) : begin(b), end(e) {};
};

void initialize(int &argc, char *argv[]) {};
void finalize() {};

enum memory_space {
  Default = 0,
  CudaSpace,
  CudaHostPinnedSpace,
  CudaUVMSpace,
  HIPSpace,
  HIPHostPinnedSpace,
  HIPManagedSpace,
  HostSpace,
  SharedSpace,
};

template<typename T, memory_space M = Default> class View {

public:
  using value_type = typename std::iterator_traits<T>::value_type;

  View<T, M>(const char *n, uint32_t s) : name{n}, size{s}, id{last_id}, mspace(M) { ++last_id; };
  View<T, M>(const View<T, M> &src) { copy(src); };
  View<T, M>(View<T, M> &&src) { copy(src); };
  ~View<T, M>() = default;

  View<T, M> &operator=(const View<T, M> &src) { copy(src); return *this; }
  View<T, M> &operator=(View<T, M> &&src) { copy(src); return *this; }
  value_type& operator()(int32_t n) {
    Klokkos::add_view_expr(id, n);
    return v;
  }

private:
  void copy(const View<T, M> &src) {
    if (this != &src) {
      v = src.v;
      name = src.name;
      size = src.size;
      id = src.id;
      mspace = src.mspace;
    }
  }

  value_type v;
  std::string name;
  uint32_t size;
  uint32_t id;
  memory_space mspace;

  static uint32_t last_id;
};
template<typename T, memory_space M> uint32_t View<T, M>::last_id = 0;

template<typename T, memory_space M> void deep_copy(View<T, M> &dst, float v) {};
template<typename T, memory_space M> void deep_copy(View<T, M> &dst, const View<T, M> &src) {};

template<typename T, memory_space M> View<T, M> create_mirror_view(const View<T, M> &src) { View<T, M> tmp(src); return tmp; };

template<typename T = int32_t>
class TeamPolicy {
public:
  TeamPolicy(int league, int team) : league_size(league), team_size(team) {};

  int32_t league_size;
  int32_t team_size;
  struct member_type {
    member_type() : policy(nullptr) {}
    member_type(const TeamPolicy<> *p) : policy(p) {}

    const TeamPolicy<> *policy;

    int32_t league_size() { return policy == nullptr? 0 : policy->league_size; }
    int32_t team_size()   { return policy == nullptr ? 0 : policy->team_size; }
    int32_t league_rank() { return Klokkos::get_league_rank(league_size(), team_size()); }
    int32_t team_rank()   { return Klokkos::get_team_rank(league_size(), team_size()); }
  };
};

template<class FunctorType> void parallel_for(int32_t n, const FunctorType &functor) {
  RangePolicy<> r{0, n};
  parallel_for(r, functor);
};

template<class FunctorType> void parallel_for(const RangePolicy<> &policy, const FunctorType &functor) {
  int32_t idx1;
  int32_t idx2;
  Klokkos::for_initialize_range(&idx1, &idx2, policy.begin, policy.end);
  functor(idx1);
  Klokkos::for_finalize();
};

template<class FunctorType> void parallel_for(const TeamPolicy<> &policy, const FunctorType &functor) {
  int32_t idx1;
  int32_t idx2;
  Kokkos::TeamPolicy<>::member_type team(&policy);
  Klokkos::for_initialize_team(&idx1, &idx2, policy.league_size, policy.team_size);
  functor(team);
  Klokkos::for_finalize();
};

}
