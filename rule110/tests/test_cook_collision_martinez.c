#include "rule110.h"
#include "glider_phases.h"
#include "cook_collisions.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef struct {
    const char *encoded;
    const char *name;
    const char *neighbor;
    int phase;
} PhaseSpec;

typedef struct {
    const char *left;
    const char *right;
    int gap;
    int contact_delta;
    size_t steps;
    const char *expected;
    const char *out0;
    const char *out1;
} CollisionCase;

static const CollisionCase CASES[] = {
    {"C1(A,f1_1)", "Ebar(B,f1_1)", 3, -39, 80, "{Ebar, C1}",
     "Ebar", "C1"},
    {"C1(A,f1_1)", "Ebar(C,f1_1)", 3, -40, 160, "{Ebar, C1}",
     "Ebar", "C1"},
    {"C2(A,f1_1)", "Ebar(C,f1_1)", 3, -40, 260, "{Ebar, C2}",
     "Ebar", "C2"},
    {"A(f1_1)", "Ebar(A,f1_1)", 4, -51, 120, "{Ebar, A}",
     "Ebar", "A"}
};

static const PhaseSpec PHASE_SPECS[] = {
    {"A(f1_1)", "A", NULL, 1},
    {"B(f4_1)", "B", NULL, 4},
    {"C1(A,f1_1)", "C1", "A", 1},
    {"C2(A,f1_1)", "C2", "A", 1},
    {"Ebar(A,f1_1)", "Ebar", "A", 1},
    {"Ebar(B,f1_1)", "Ebar", "B", 1},
    {"Ebar(C,f1_1)", "Ebar", "C", 1},
    {"F(A,f1_1)", "F", "A", 1}
};

static const char *NEIGHBORS[] = {NULL, "A", "B", "C", "D"};

static const PhaseSpec *phase_spec_for(const char *encoded) {
    for (size_t i = 0; i < sizeof(PHASE_SPECS) / sizeof(PHASE_SPECS[0]); i++) {
        if (strcmp(encoded, PHASE_SPECS[i].encoded) == 0) {
            return &PHASE_SPECS[i];
        }
    }
    return NULL;
}

static void fill_ether(uint8_t *cells, size_t len) {
    size_t ether_len = 0;
    const char *ether = glider_phase("ether", NULL, 1, &ether_len);

    if (ether == NULL || ether_len == 0) abort();
    for (size_t i = 0; i < len; i++) {
        cells[i] = (uint8_t)(ether[i % ether_len] == '1');
    }
}

static int emit_spec(uint8_t *cells,
                     size_t len,
                     size_t pos,
                     const PhaseSpec *spec,
                     size_t *written_out) {
    size_t phase_len = 0;
    const char *bits = NULL;

    if (written_out != NULL) *written_out = 0;
    if (spec == NULL) return 1;
    bits = glider_phase(spec->name, spec->neighbor, spec->phase, &phase_len);
    if (bits == NULL || pos > len || phase_len > len - pos) return 1;

    for (size_t i = 0; i < phase_len; i++) {
        cells[pos + i] = (uint8_t)(bits[i] == '1');
    }
    if (written_out != NULL) *written_out = phase_len;
    return 0;
}

static size_t count_diff(const uint8_t *cells,
                         const uint8_t *ether,
                         size_t len) {
    size_t diff = 0;

    for (size_t i = 0; i < len; i++) {
        if (cells[i] != ether[i]) diff++;
    }
    return diff;
}

static size_t count_diff_islands(const uint8_t *cells,
                                 const uint8_t *ether,
                                 size_t len) {
    size_t count = 0;
    size_t quiet_gap = 0;
    int in_island = 0;

    for (size_t i = 0; i < len; i++) {
        if (cells[i] != ether[i]) {
            if (!in_island) {
                count++;
                in_island = 1;
            }
            quiet_gap = 0;
        } else if (in_island) {
            quiet_gap++;
            if (quiet_gap > 3u) {
                in_island = 0;
                quiet_gap = 0;
            }
        }
    }
    return count;
}

static int window_has_diff(const uint8_t *cells,
                           const uint8_t *ether,
                           size_t pos,
                           size_t phase_len) {
    for (size_t i = 0; i < phase_len; i++) {
        if (cells[pos + i] != ether[pos + i]) return 1;
    }
    return 0;
}

static int match_phase_at(const uint8_t *cells,
                          const uint8_t *ether,
                          size_t len,
                          size_t pos,
                          const char *name,
                          const char *neighbor,
                          int phase) {
    size_t phase_len = 0;
    const char *bits = glider_phase(name, neighbor, phase, &phase_len);

    if (bits == NULL || pos > len || phase_len > len - pos) return 0;
    if (!window_has_diff(cells, ether, pos, phase_len)) return 0;
    for (size_t i = 0; i < phase_len; i++) {
        if (cells[pos + i] != (uint8_t)(bits[i] == '1')) return 0;
    }
    return 1;
}

static int detect_glider(const uint8_t *cells,
                         const uint8_t *ether,
                         size_t len,
                         const char *name) {
    for (size_t pos = 0; pos < len; pos++) {
        for (size_t n = 0; n < sizeof(NEIGHBORS) / sizeof(NEIGHBORS[0]); n++) {
            for (int phase = 1; phase <= 4; phase++) {
                if (match_phase_at(cells,
                                   ether,
                                   len,
                                   pos,
                                   name,
                                   NEIGHBORS[n],
                                   phase)) {
                    return 1;
                }
            }
        }
    }
    return 0;
}

static int verify_collision(const CollisionCase *tc) {
    enum { W = 1800 };
    uint8_t cells[W];
    uint8_t ether[W];
    const PhaseSpec *left = phase_spec_for(tc->left);
    const PhaseSpec *right = phase_spec_for(tc->right);
    size_t pos1 = 600;
    size_t pos2 = 0;
    size_t left_len = 0;
    const char *lookup = cook_collision_lookup(tc->left, tc->right, tc->gap);
    size_t before_diff = 0;
    size_t before_islands = 0;
    size_t after_diff = 0;
    size_t after_islands = 0;
    int detected0 = 0;
    int detected1 = 0;

    if (lookup == NULL) {
        printf("  %s / %s: FAIL missing cook collision row\n",
               tc->left,
               tc->right);
        return 1;
    }
    if (strcmp(lookup, tc->expected) != 0) {
        printf("  %s / %s: FAIL lookup=%s expected=%s\n",
               tc->left,
               tc->right,
               lookup,
               tc->expected);
        return 1;
    }

    fill_ether(cells, W);
    fill_ether(ether, W);
    if (emit_spec(cells, W, pos1, left, &left_len)) {
        printf("  %s / %s: FAIL missing left phase\n", tc->left, tc->right);
        return 1;
    }
    pos2 = (size_t)((long)pos1 + (long)left_len +
                    ((long)tc->gap * 14L) + (long)tc->contact_delta);
    if (emit_spec(cells, W, pos2, right, NULL)) {
        printf("  %s / %s: FAIL missing right phase\n", tc->left, tc->right);
        return 1;
    }

    before_diff = count_diff(cells, ether, W);
    before_islands = count_diff_islands(cells, ether, W);
    r110_run_n_steps(cells, W, tc->steps);
    r110_run_n_steps(ether, W, tc->steps);
    after_diff = count_diff(cells, ether, W);
    after_islands = count_diff_islands(cells, ether, W);
    detected0 = detect_glider(cells, ether, W, tc->out0);
    detected1 = detect_glider(cells, ether, W, tc->out1);

    if (before_diff == 0u || before_islands < 2u ||
        after_diff == before_diff || !detected0 || !detected1) {
        printf("  %s -%d e- %s -> %s: FAIL diff %zu/%zu islands %zu/%zu\n",
               tc->left,
               tc->gap,
               tc->right,
               lookup,
               before_diff,
               after_diff,
               before_islands,
               after_islands);
        return 1;
    }

    printf("  %s -%d e- %s -> %s: PASS diff %zu/%zu islands %zu/%zu\n",
           tc->left,
           tc->gap,
           tc->right,
           lookup,
           before_diff,
           after_diff,
           before_islands,
           after_islands);
    return 0;
}

static int verify_lookup_accessors(void) {
    size_t checked = 0;

    for (size_t i = 0; i < cook_collision_lookup_count(); i++) {
        const char *left = cook_collision_lookup_left(i);
        const char *right = cook_collision_lookup_right(i);
        int gap = cook_collision_lookup_gap(i);
        const char *result = cook_collision_lookup_result(i);

        if (left == NULL || right == NULL || result == NULL) return 1;
        if (cook_collision_lookup(left, right, gap) != result) return 1;
        checked++;
    }

    if (checked < 18u) return 1;
    printf("  cook collision lookup table: PASS\n");
    return 0;
}

int main(void) {
    int fail = 0;

    printf("== test_cook_collision_martinez ==\n");
    fail += verify_lookup_accessors();
    for (size_t i = 0; i < sizeof(CASES) / sizeof(CASES[0]); i++) {
        fail += verify_collision(&CASES[i]);
    }

    if (fail) {
        printf("FAIL %d collision verifier mismatch(es)\n", fail);
        return 1;
    }

    printf("ALL test_cook_collision_martinez tests passed\n");
    return 0;
}
