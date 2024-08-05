
#include <cstddef>
#include <cstdint>
#include <string>
#include <klee/klokkos.h>

#define KOKKOS_LAMBDA [&]

#define HOST_SPACE 0
#define DEVICE_SPACE 1

namespace Kokkos
{

uint32_t AUTO = 0;
uint32_t kokkos_default_space;
uint32_t kokkos_team_size = 1;
#define KOKKOS_MAX_TEAM_SIZE 4096


template<typename UNUSED = char> struct RangePolicy {
  int32_t begin;
  int32_t end;
  RangePolicy(int32_t b, int32_t e) : begin(b), end(e) {};
};

void initialize(int &argc, char *argv[]) {
  klee_make_symbolic(&kokkos_default_space, sizeof(kokkos_default_space), "kokkos_default_space");
  klee_assume(kokkos_default_space <= DEVICE_SPACE);
  Klokkos::kokkos_initialize(kokkos_default_space);
  klee_make_symbolic(&kokkos_team_size, sizeof(kokkos_team_size), "kokkos_team_size");
  klee_assume(kokkos_team_size < KOKKOS_MAX_TEAM_SIZE);
};
void finalize() {
  Klokkos::kokkos_finalize();
};

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
  using HostMirror = typename Kokkos::View<T, M>;

  View<T, M>(const char *n, uint32_t s) : name{n}, size{s}, id{last_id}, mspace(M) {
    if (M == Default) {
      mspace = kokkos_default_space;
    } else if (M == HostSpace) {
      mspace = HOST_SPACE;
    } else {
      mspace = DEVICE_SPACE;
    }
    ++last_id;
    Klokkos::on_view_create(id, size, mspace);
  };
  View<T, M>(const View<T, M> &src) { copy(src); };
  View<T, M>(View<T, M> &&src) { copy(src); };
  ~View<T, M>() = default;

  View<T, M> &operator=(const View<T, M> &src) { copy(src); return *this; }
  View<T, M> &operator=(View<T, M> &&src) { copy(src); return *this; }
  value_type& operator()(int32_t n) {
    Klokkos::on_view_reference(id, n);
    return v;
  }

  uint32_t extent() const {
    return size;
  }

  value_type v;
  std::string name;
  uint32_t size;
  uint32_t id;
  uint32_t mspace;
  static uint32_t last_id;

  void copy(const View<T, M> &src) {
    if (this != &src) {
      v = src.v;
      name = src.name;
      size = src.size;
      id = src.id;
      mspace = src.mspace;
    }
  }

};
template<typename T, memory_space M> uint32_t View<T, M>::last_id = 1;

template<typename T, memory_space M> void deep_copy(View<T, M> &dst, float v) {};

template<typename T, memory_space M> void deep_copy(View<T, M> &dst, const View<T, M> &src) {
    Klokkos::view_deep_copy(dst.extent(), src.extent());
    Klokkos::on_deep_copy(dst.id, src.id);
};

template<typename T, memory_space M> View<T, M> create_mirror_view(const View<T, M> &src) {
  View<T, M> tmp(src);
  tmp.mspace = HOST_SPACE;
  tmp.id = View<T, M>::last_id++;
  Klokkos::on_view_create(tmp.id, tmp.size, tmp.mspace);
  Klokkos::on_view_mirror(src.id, tmp.id);
  return tmp;
};

template<typename T = int32_t>
class TeamPolicy {
public:
  TeamPolicy(int league, int team) : league_size(league) {};

  int32_t league_size;
  struct member_type {
    member_type() : policy(nullptr), idx(nullptr) {}
    member_type(const TeamPolicy<> *p, int32_t *i) : policy(p), idx(i) {}

    const TeamPolicy<> *policy;
    int32_t *idx;

    int32_t league_size() { return policy == nullptr? 0 : policy->league_size; }
    int32_t team_size()   { return policy == nullptr ? 0 : 1; }
    int32_t league_rank() { return policy == nullptr ? 0 : 0; }
    int32_t team_rank() { return policy == nullptr ? 0 : *idx; }
  };
};

template<class FunctorType> void parallel_for(int32_t n, const FunctorType &functor) {
  int32_t idx1;
  int32_t idx2;
  Klokkos::for_initialize(kokkos_default_space, &idx1, &idx2, 0, n);
  klee_open_merge();
  functor(idx1);
  klee_close_merge();
  Klokkos::for_finalize();
};

template<class FunctorType> void parallel_for(const RangePolicy<> &policy, const FunctorType &functor) {
  int32_t idx1;
  int32_t idx2;
  Klokkos::for_initialize(kokkos_default_space, &idx1, &idx2, policy.begin, policy.end);
  klee_open_merge();
  functor(idx1);
  klee_close_merge();
  Klokkos::for_finalize();
};

template<class FunctorType> void parallel_for(const TeamPolicy<> &policy, const FunctorType &functor) {
  int32_t idx1;
  int32_t idx2;
  Kokkos::TeamPolicy<>::member_type team(&policy, &idx1);
  Klokkos::for_initialize(kokkos_default_space, &idx1, &idx2, 0, kokkos_team_size);
  klee_open_merge();
  functor(team);
  klee_close_merge();
  Klokkos::for_finalize();
};

}
