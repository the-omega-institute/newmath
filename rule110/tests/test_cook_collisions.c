#include "cook_collisions.h"
#include <assert.h>
#include <stdio.h>

static const char *outcome_name(CollisionOutcome outcome) {
    switch (outcome) {
    case COLLISION_ANNIHILATION:
        return "annihilation";
    case COLLISION_PASSTHROUGH:
        return "passthrough";
    case COLLISION_NEW_PARTICLES:
        return "new_particles";
    case COLLISION_UNKNOWN:
        return "unknown";
    default:
        return "unknown";
    }
}

static const char *evidence_name(CollisionEvidence evidence) {
    switch (evidence) {
    case COLLISION_EVIDENCE_HEURISTIC:
        return "heuristic";
    case COLLISION_EVIDENCE_DIRECT_SIM:
        return "direct_sim";
    case COLLISION_EVIDENCE_PHASES_PENDING:
        return "phases_pending";
    default:
        return "heuristic";
    }
}

static void test_AA_direct_simulation_entry(void) {
    const CookGliderPattern *glider_A = cook_collision_glider_A_pattern();
    CollisionResult direct = cook_simulate_collision_patterns(
        glider_A,
        glider_A,
        448,
        9,
        220);
    CollisionResult lookup = cook_lookup_collision('A', 'A', 9);

    assert(glider_A != NULL);
    assert(glider_A->glider == 'A');
    assert(glider_A->phase == 0);
    assert(glider_A->width == 6);
    assert(glider_A->velocity_num == 2);
    assert(glider_A->velocity_den == 3);

    assert(direct.left_glider == 'A');
    assert(direct.right_glider == 'A');
    assert(direct.evidence == COLLISION_EVIDENCE_DIRECT_SIM);
    assert(direct.left_phase == 0);
    assert(direct.right_phase == 0);
    assert(direct.separation == 9);
    assert(direct.outcome == COLLISION_PASSTHROUGH);
    assert(direct.final_diff_count == 12);
    assert(direct.product_count == 0);
    assert(direct.unmatched_island_count == 1);

    assert(lookup.left_glider == 'A');
    assert(lookup.right_glider == 'A');
    assert(lookup.evidence == COLLISION_EVIDENCE_DIRECT_SIM);
    assert(lookup.left_phase == direct.left_phase);
    assert(lookup.right_phase == direct.right_phase);
    assert(lookup.separation == direct.separation);
    assert(lookup.outcome == direct.outcome);
    assert(lookup.final_diff_count == direct.final_diff_count);
    assert(lookup.product_count == direct.product_count);
    assert(lookup.unmatched_island_count == direct.unmatched_island_count);

    printf("  A_A_direct_simulation_entry: PASS\n");
}

static void test_non_AA_rows_remain_phase_pending(void) {
    CollisionResult result = cook_lookup_collision('A', 'B', 9);

    assert(result.left_glider == 'A');
    assert(result.right_glider == 'B');
    assert(result.evidence == COLLISION_EVIDENCE_PHASES_PENDING);
    assert(result.outcome == COLLISION_UNKNOWN);
    assert(result.product_count == 0);

    printf("  non_AA_rows_remain_phase_pending: PASS\n");
}

int main(void) {
    static const char gliders[] = {'A', 'B', 'C', 'D'};
    const size_t pos1 = 420;
    const size_t pos2 = 560;
    const size_t steps = 220;

    printf("== test_cook_collisions ==\n");
    test_AA_direct_simulation_entry();
    test_non_AA_rows_remain_phase_pending();
    printf("left right pos1 pos2 steps outcome evidence final_diff\n");

    for (size_t i = 0; i < sizeof(gliders) / sizeof(gliders[0]); i++) {
        for (size_t j = 0; j < sizeof(gliders) / sizeof(gliders[0]); j++) {
            CollisionResult result = cook_simulate_collision(
                gliders[i],
                gliders[j],
                pos1,
                pos2,
                steps);

            printf("%c %c %zu %zu %zu %s %s %zu\n",
                   result.left_glider,
                   result.right_glider,
                   pos1,
                   pos2,
                   steps,
                   outcome_name(result.outcome),
                   evidence_name(result.evidence),
                   result.final_diff_count);
        }
    }

    printf("ALL test_cook_collisions tests passed\n");
    return 0;
}
