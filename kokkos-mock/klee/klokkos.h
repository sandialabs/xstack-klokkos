
#ifndef KLOKKOS_H
#define KLOKKOS_H

#include <stdint.h>
#include <klee/klee.h>

#ifdef __cplusplus
extern "C" {
#endif

namespace Klokkos
{
void kokkos_initialize(uint32_t kokkos_default_space);
void kokkos_finalize();
void on_view_create(uint32_t id, uint32_t size, uint32_t mspace);
void on_view_mirror(uint32_t id, uint32_t host);
void on_view_reference(int32_t id, uintptr_t expr);
void on_deep_copy(uint32_t dst, uint32_t src);
void for_initialize(int32_t space, int32_t *idx1, int32_t *idx2, int32_t begin, int32_t end);
void for_finalize();
void view_deep_copy(int32_t dst_size, int32_t src_size);
}

#ifdef __cplusplus
}
#endif

#endif /* KLOKKOS_H */
