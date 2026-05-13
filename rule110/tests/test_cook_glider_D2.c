#include "cook_glider_D2.h"
#include "glider_phases.h"
#include "rule110.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void fill_repeated_phase(uint8_t *cells,
                                size_t repeat_count,
                                const char *bits,
                                size_t len) {
    for (size_t repeat = 0; repeat < repeat_count; repeat++) {
        for (size_t i = 0; i < len; i++) {
            cells[(repeat * len) + i] = (uint8_t)(bits[i] == '1');
        }
    }
}

static void test_gliderD2_moves(void) {
    const char *bits = NULL;
    const size_t repeat_count = 9;
    const int displacement = 2;
    size_t phase_len = 0;
    size_t center = 0;
    size_t tape_len = 0;
    uint8_t *before = NULL;
    uint8_t *after = NULL;

    bits = glider_phase("D2", "A", 1, &phase_len);
    assert(bits != NULL);
    assert(phase_len == COOK_GLIDER_D2_WIDTH);

    center = (repeat_count / 2u) * phase_len;
    tape_len = repeat_count * phase_len;
    before = (uint8_t *)malloc(tape_len);
    after = (uint8_t *)malloc(tape_len);
    assert(before != NULL);
    assert(after != NULL);

    fill_repeated_phase(before, repeat_count, bits, phase_len);
    memcpy(after, before, tape_len);

    r110_run_n_steps(after, tape_len, COOK_GLIDER_D2_PERIOD);

    for (size_t i = 0; i < phase_len; i++) {
        size_t src = center + i - (size_t)displacement;
        assert(after[center + i] == before[src]);
    }

    free(after);
    free(before);
    printf("  gliderD2_moves: PASS\n");
}

static void test_gliderD2_ether_unaffected(void) {
    const char *bits = NULL;
    const size_t repeat_count = 9;
    const int displacement = 2;
    size_t phase_len = 0;
    size_t center = 0;
    size_t len = 0;
    uint8_t *before = NULL;
    uint8_t *cells = NULL;

    bits = glider_phase("D2", "A", 1, &phase_len);
    assert(bits != NULL);
    center = (repeat_count / 2u) * phase_len;
    len = repeat_count * phase_len;
    before = (uint8_t *)malloc(len);
    cells = (uint8_t *)malloc(len);
    assert(before != NULL);
    assert(cells != NULL);

    fill_repeated_phase(before, repeat_count, bits, phase_len);
    memcpy(cells, before, len);
    assert(cook_glider_D2_emit_phase_exact(cells, center, len, "A", 1) == 0);

    r110_run_n_steps(cells, len, COOK_GLIDER_D2_PERIOD);

    for (size_t i = phase_len; i < center - phase_len; i++) {
        size_t src = i - (size_t)displacement;

        assert(cells[i] == before[src]);
    }
    for (size_t i = center + (2u * phase_len); i < len - phase_len; i++) {
        size_t src = i - (size_t)displacement;

        assert(cells[i] == before[src]);
    }

    free(cells);
    free(before);
    printf("  gliderD2_ether_unaffected: PASS\n");
}

int main(void) {
    printf("== test_cook_glider_D2 ==\n");
    test_gliderD2_moves();
    test_gliderD2_ether_unaffected();
    printf("ALL test_cook_glider_D2 tests passed\n");
    return 0;
}
