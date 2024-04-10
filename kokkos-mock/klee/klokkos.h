
#ifndef KLOKKOS_H
#define KLOKKOS_H

#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

namespace Klokkos
{
void add_view_expr(int32_t id, uintptr_t expr);
void for_initialize_range(int32_t *idx1, int32_t *idx2, int32_t begin, int32_t end);
void for_initialize_team(int32_t *idx1, int32_t *idx2, int32_t league_size, int32_t team_size);
int32_t get_league_rank(int32_t league, int32_t team);
int32_t get_team_rank(int32_t league, int32_t team);
void for_finalize();
}

#ifdef __cplusplus
}
#endif

#endif /* KLOKKOS_H */
