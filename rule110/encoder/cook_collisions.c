#include "cook_collisions.h"
#include "cook_construction.h"
#include "cook_glider_B.h"
#include "cook_glider_C.h"
#include "cook_glider_D.h"
#include "rule110.h"
#include <stdint.h>
#include <stdlib.h>

typedef struct {
    size_t diff_count;
    size_t cluster_count;
} CollisionObservation;

static size_t glider_width(char glider) {
    switch (glider) {
    case 'A': return 4;
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

CollisionResult cook_simulate_collision(char left,
                                         char right,
                                         size_t pos1,
                                         size_t pos2,
                                         size_t steps) {
    CollisionResult result;
    CollisionObservation before;
    CollisionObservation after;
    const size_t guard = COOK_ETHER_WIDTH * 16;
    size_t right_width = glider_width(right);
    size_t min_len = 0;
    size_t period_count = 0;
    size_t len = 0;
    uint8_t *cells = NULL;
    uint8_t *ether = NULL;

    result.left_glider = left;
    result.right_glider = right;
    result.outcome = COLLISION_UNKNOWN;

    if (!is_supported_glider(left) || !is_supported_glider(right)) {
        return result;
    }

    if (pos2 <= pos1) {
        return result;
    }

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

    free(cells);
    free(ether);

    return result;
}
