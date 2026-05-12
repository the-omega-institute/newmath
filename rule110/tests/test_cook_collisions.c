#include "cook_collisions.h"
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

int main(void) {
    static const char gliders[] = {'A', 'B', 'C', 'D'};
    const size_t pos1 = 420;
    const size_t pos2 = 560;
    const size_t steps = 220;

    printf("== test_cook_collisions ==\n");
    printf("left right pos1 pos2 steps outcome\n");

    for (size_t i = 0; i < sizeof(gliders) / sizeof(gliders[0]); i++) {
        for (size_t j = 0; j < sizeof(gliders) / sizeof(gliders[0]); j++) {
            CollisionResult result = cook_simulate_collision(
                gliders[i],
                gliders[j],
                pos1,
                pos2,
                steps);

            printf("%c %c %zu %zu %zu %s\n",
                   result.left_glider,
                   result.right_glider,
                   pos1,
                   pos2,
                   steps,
                   outcome_name(result.outcome));
        }
    }

    return 0;
}
