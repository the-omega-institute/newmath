#ifndef COOK_COLLISIONS_H
#define COOK_COLLISIONS_H

#include <stddef.h>
#include <stdint.h>

#define COOK_COLLISION_MAX_PRODUCTS 4

typedef enum {
    COLLISION_ANNIHILATION  = 0,
    COLLISION_PASSTHROUGH   = 1,
    COLLISION_NEW_PARTICLES = 2,
    COLLISION_UNKNOWN       = 3
} CollisionOutcome;

typedef enum {
    COLLISION_EVIDENCE_HEURISTIC        = 0,
    COLLISION_EVIDENCE_DIRECT_SIM       = 1,
    COLLISION_EVIDENCE_PHASES_PENDING   = 2
} CollisionEvidence;

typedef struct {
    const uint8_t *row;
    size_t width;
    char glider;
    size_t phase;
    int velocity_num;
    int velocity_den;
} CookGliderPattern;

typedef struct {
    char glider;
    size_t phase;
    int velocity_num;
    int velocity_den;
    size_t start;
    size_t end;
} CollisionProduct;

typedef struct {
    char left_glider;
    char right_glider;
    CollisionOutcome outcome;
    CollisionEvidence evidence;
    size_t left_phase;
    size_t right_phase;
    size_t separation;
    size_t product_count;
    CollisionProduct products[COOK_COLLISION_MAX_PRODUCTS];
    size_t unmatched_island_count;
    size_t final_diff_count;
} CollisionResult;

const CookGliderPattern *cook_collision_glider_A_pattern(void);

CollisionResult cook_simulate_collision_patterns(const CookGliderPattern *left,
                                                 const CookGliderPattern *right,
                                                 size_t left_pos,
                                                 size_t separation,
                                                 size_t steps);

CollisionResult cook_lookup_collision(char left,
                                       char right,
                                       size_t separation_mod);

CollisionResult cook_simulate_collision(char left,
                                         char right,
                                         size_t pos1,
                                         size_t pos2,
                                         size_t steps);

#endif
