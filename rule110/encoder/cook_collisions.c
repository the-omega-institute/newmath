#include "cook_collisions.h"
#include "cook_construction.h"
#include "cook_glider_B.h"
#include "cook_glider_C.h"
#include "cook_glider_D.h"
#include "rule110.h"
#include <stdint.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    size_t diff_count;
    size_t cluster_count;
} CollisionObservation;

typedef struct {
    size_t start;
    size_t end;
} DiffIsland;

static const uint8_t GLIDER_A_PHASE_0[6] = {1, 1, 1, 1, 1, 0};

static const CookGliderPattern GLIDER_A_PATTERN = {
    GLIDER_A_PHASE_0,
    sizeof(GLIDER_A_PHASE_0),
    'A',
    0,
    2,
    3
};

const CookGliderPattern *cook_collision_glider_A_pattern(void) {
    return &GLIDER_A_PATTERN;
}

static size_t glider_width(char glider) {
    switch (glider) {
    case 'A': return GLIDER_A_PATTERN.width;
    case 'B': return COOK_GLIDER_B_WIDTH;
    case 'C': return COOK_GLIDER_C_WIDTH;
    case 'D': return COOK_GLIDER_D_WIDTH;
    default: return 0;
    }
}

static int is_supported_glider(char glider) {
    return glider_width(glider) != 0;
}

static void emit_glider(char glider, uint8_t *cells, size_t pos, size_t len) {
    switch (glider) {
    case 'A':
        cook_glider_A_emit(cells, pos, len);
        break;
    case 'B':
        cook_glider_B_emit(cells, pos, len);
        break;
    case 'C':
        cook_glider_C_emit(cells, pos, len);
        break;
    case 'D':
        cook_glider_D_emit(cells, pos, len);
        break;
    default:
        break;
    }
}

static void emit_pattern(const CookGliderPattern *pattern,
                         uint8_t *cells,
                         size_t pos,
                         size_t len) {
    if (pattern == NULL || pattern->row == NULL) return;
    if (pos > len || pattern->width > len - pos) return;

    memcpy(cells + pos, pattern->row, pattern->width);
}

static CollisionObservation observe_perturbations(const uint8_t *cells,
                                                  const uint8_t *ether,
                                                  size_t len) {
    CollisionObservation obs;
    size_t quiet_gap = 0;
    int in_cluster = 0;

    obs.diff_count = 0;
    obs.cluster_count = 0;

    for (size_t i = 0; i < len; i++) {
        if (cells[i] != ether[i]) {
            obs.diff_count++;
            if (!in_cluster) {
                obs.cluster_count++;
                in_cluster = 1;
            }
            quiet_gap = 0;
        } else if (in_cluster) {
            quiet_gap++;
            if (quiet_gap > 3) {
                in_cluster = 0;
                quiet_gap = 0;
            }
        }
    }

    return obs;
}

static size_t collect_islands(const uint8_t *cells,
                              const uint8_t *ether,
                              size_t len,
                              DiffIsland *islands,
                              size_t island_capacity) {
    size_t count = 0;
    size_t quiet_gap = 0;
    size_t start = 0;
    size_t last = 0;
    int in_cluster = 0;

    for (size_t i = 0; i < len; i++) {
        if (cells[i] != ether[i]) {
            if (!in_cluster) {
                start = i;
                in_cluster = 1;
            }
            last = i;
            quiet_gap = 0;
        } else if (in_cluster) {
            quiet_gap++;
            if (quiet_gap > 3) {
                if (count < island_capacity) {
                    islands[count].start = start;
                    islands[count].end = last;
                }
                count++;
                in_cluster = 0;
                quiet_gap = 0;
            }
        }
    }

    if (in_cluster) {
        if (count < island_capacity) {
            islands[count].start = start;
            islands[count].end = last;
        }
        count++;
    }

    return count;
}

static int island_matches_glider_A(const uint8_t *cells,
                                   const uint8_t *ether,
                                   size_t len,
                                   DiffIsland island) {
    if (island.end < island.start) return 0;
    if (island.end + 1 < GLIDER_A_PATTERN.width) return 0;

    for (size_t pos = island.start; pos + GLIDER_A_PATTERN.width <= island.end + 1;
         pos++) {
        uint8_t trial[6];
        size_t diff_count = 0;

        memcpy(trial, ether + pos, sizeof(trial));
        memcpy(trial, GLIDER_A_PATTERN.row, sizeof(trial));

        for (size_t i = island.start; i <= island.end && i < len; i++) {
            uint8_t expected = ether[i];
            if (i >= pos && i < pos + sizeof(trial)) {
                expected = trial[i - pos];
            }
            if (cells[i] != expected) diff_count++;
        }

        if (diff_count == 0) return 1;
    }

    return 0;
}

static CollisionOutcome classify_observation(CollisionObservation before,
                                             CollisionObservation after) {
    size_t cluster_delta = 0;

    if (before.diff_count == 0 || before.cluster_count == 0) {
        return COLLISION_UNKNOWN;
    }

    if (after.diff_count == 0 || after.cluster_count == 0) {
        return COLLISION_ANNIHILATION;
    }

    if (after.cluster_count > before.cluster_count) {
        return COLLISION_NEW_PARTICLES;
    }

    cluster_delta = (before.cluster_count > after.cluster_count)
        ? before.cluster_count - after.cluster_count
        : after.cluster_count - before.cluster_count;

    if (cluster_delta <= 1) {
        return COLLISION_PASSTHROUGH;
    }

    return COLLISION_UNKNOWN;
}

static CollisionResult empty_result(char left, char right) {
    CollisionResult result;

    memset(&result, 0, sizeof(result));
    result.left_glider = left;
    result.right_glider = right;
    result.outcome = COLLISION_UNKNOWN;
    result.evidence = COLLISION_EVIDENCE_HEURISTIC;

    return result;
}

static void classify_products(CollisionResult *result,
                              const uint8_t *cells,
                              const uint8_t *ether,
                              size_t len) {
    DiffIsland islands[16];
    size_t island_count = collect_islands(cells,
                                          ether,
                                          len,
                                          islands,
                                          sizeof(islands) / sizeof(islands[0]));

    result->unmatched_island_count = island_count;

    for (size_t i = 0; i < island_count &&
         i < sizeof(islands) / sizeof(islands[0]); i++) {
        if (island_matches_glider_A(cells, ether, len, islands[i])) {
            size_t product_index = result->product_count;

            if (product_index < COOK_COLLISION_MAX_PRODUCTS) {
                result->products[product_index].glider = 'A';
                result->products[product_index].phase = 0;
                result->products[product_index].velocity_num =
                    GLIDER_A_PATTERN.velocity_num;
                result->products[product_index].velocity_den =
                    GLIDER_A_PATTERN.velocity_den;
                result->products[product_index].start = islands[i].start;
                result->products[product_index].end = islands[i].end;
                result->product_count++;
            }
            if (result->unmatched_island_count > 0) {
                result->unmatched_island_count--;
            }
        }
    }
}

CollisionResult cook_simulate_collision_patterns(const CookGliderPattern *left,
                                                 const CookGliderPattern *right,
                                                 size_t left_pos,
                                                 size_t separation,
                                                 size_t steps) {
    CollisionResult result;
    CollisionObservation before;
    CollisionObservation after;
    const size_t guard = COOK_ETHER_WIDTH * 32;
    size_t right_pos = 0;
    size_t min_len = 0;
    size_t period_count = 0;
    size_t len = 0;
    uint8_t *cells = NULL;
    uint8_t *ether = NULL;

    if (left == NULL || right == NULL) {
        return empty_result('?', '?');
    }

    result = empty_result(left->glider, right->glider);
    result.evidence = COLLISION_EVIDENCE_DIRECT_SIM;
    result.left_phase = left->phase;
    result.right_phase = right->phase;
    result.separation = separation;

    right_pos = left_pos + separation;
    if (right_pos <= left_pos) {
        result.evidence = COLLISION_EVIDENCE_PHASES_PENDING;
        return result;
    }

    min_len = right_pos + right->width + steps + guard + 1;
    period_count = (min_len + COOK_ETHER_WIDTH - 1) / COOK_ETHER_WIDTH;
    len = period_count * COOK_ETHER_WIDTH;

    cells = (uint8_t *)malloc(len);
    ether = (uint8_t *)malloc(len);
    if (cells == NULL || ether == NULL) {
        free(cells);
        free(ether);
        return result;
    }

    cook_ether_emit(cells, period_count);
    cook_ether_emit(ether, period_count);

    emit_pattern(left, cells, left_pos, len);
    emit_pattern(right, cells, right_pos, len);

    before = observe_perturbations(cells, ether, len);

    r110_run_n_steps(cells, len, steps);
    r110_run_n_steps(ether, len, steps);

    after = observe_perturbations(cells, ether, len);
    result.outcome = classify_observation(before, after);
    result.final_diff_count = after.diff_count;
    classify_products(&result, cells, ether, len);

    free(cells);
    free(ether);

    return result;
}

CollisionResult cook_lookup_collision(char left,
                                       char right,
                                       size_t separation_mod) {
    CollisionResult result = empty_result(left, right);

    result.separation = separation_mod;

    if (left == 'A' && right == 'A') {
        return cook_simulate_collision_patterns(&GLIDER_A_PATTERN,
                                                &GLIDER_A_PATTERN,
                                                COOK_ETHER_WIDTH * 32,
                                                separation_mod,
                                                220);
    }

    if (is_supported_glider(left) && is_supported_glider(right)) {
        result.evidence = COLLISION_EVIDENCE_PHASES_PENDING;
    }

    return result;
}

CollisionResult cook_simulate_collision(char left,
                                         char right,
                                         size_t pos1,
                                         size_t pos2,
                                         size_t steps) {
    CollisionResult result = empty_result(left, right);
    CollisionObservation before;
    CollisionObservation after;
    const size_t guard = COOK_ETHER_WIDTH * 16;
    size_t right_width = glider_width(right);
    size_t min_len = 0;
    size_t period_count = 0;
    size_t len = 0;
    uint8_t *cells = NULL;
    uint8_t *ether = NULL;

    if (!is_supported_glider(left) || !is_supported_glider(right)) {
        return result;
    }

    if (pos2 <= pos1) {
        return result;
    }

    result.separation = pos2 - pos1;

    min_len = pos2 + right_width + steps + guard + 1;
    period_count = (min_len + COOK_ETHER_WIDTH - 1) / COOK_ETHER_WIDTH;
    len = period_count * COOK_ETHER_WIDTH;

    cells = (uint8_t *)malloc(len);
    ether = (uint8_t *)malloc(len);
    if (cells == NULL || ether == NULL) {
        free(cells);
        free(ether);
        return result;
    }

    cook_ether_emit(cells, period_count);
    cook_ether_emit(ether, period_count);

    emit_glider(left, cells, pos1, len);
    emit_glider(right, cells, pos2, len);

    before = observe_perturbations(cells, ether, len);

    r110_run_n_steps(cells, len, steps);
    r110_run_n_steps(ether, len, steps);

    after = observe_perturbations(cells, ether, len);
    result.outcome = classify_observation(before, after);
    result.final_diff_count = after.diff_count;

    free(cells);
    free(ether);

    return result;
}
