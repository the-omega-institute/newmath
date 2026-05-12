#ifndef COOK_COLLISIONS_H
#define COOK_COLLISIONS_H

#include <stddef.h>

typedef enum {
    COLLISION_ANNIHILATION  = 0,
    COLLISION_PASSTHROUGH   = 1,
    COLLISION_NEW_PARTICLES = 2,
    COLLISION_UNKNOWN       = 3
} CollisionOutcome;

typedef struct {
    char left_glider;
    char right_glider;
    CollisionOutcome outcome;
} CollisionResult;

CollisionResult cook_simulate_collision(char left,
                                         char right,
                                         size_t pos1,
                                         size_t pos2,
                                         size_t steps);

#endif
