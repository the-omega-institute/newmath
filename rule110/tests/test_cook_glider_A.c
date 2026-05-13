#include "cook_construction.h"
#include "rule110.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const uint8_t GLIDER_A_F1_1[6] = {1, 1, 1, 1, 1, 0};
static const uint8_t GLIDER_A_F1_1_STEP_1[6] = {1, 0, 0, 0, 1, 1};
static const uint8_t GLIDER_A_F1_1_STEP_2[6] = {1, 0, 0, 1, 1, 0};
static const uint8_t GLIDER_A_F1_1_STEP_3[6] = {1, 0, 1, 1, 1, 1};

static uint8_t rule110_periodic_cell(const uint8_t *cells,
                                     size_t len,
                                     size_t pos) {
    uint8_t left = cells[(pos + len - 1) % len];
    uint8_t self = cells[pos];
    uint8_t right = cells[(pos + 1) % len];
    size_t table_index = ((size_t)left << 2) | ((size_t)self << 1) | right;
    static const uint8_t table[8] = {0, 1, 1, 1, 0, 1, 1, 0};

    return table[table_index];
}

static void periodic_step(uint8_t *cells, size_t len) {
    uint8_t next[sizeof(GLIDER_A_F1_1)];

    assert(len == sizeof(next));
    for (size_t i = 0; i < len; i++) {
        next[i] = rule110_periodic_cell(cells, len, i);
    }
    memcpy(cells, next, len);
}

static uint8_t ether_cell_at_step(size_t pos, size_t step_count) {
    size_t shift = (4 * step_count) % COOK_ETHER_WIDTH;
    return COOK_ETHER_PATTERN[(pos + shift) % COOK_ETHER_WIDTH];
}

static size_t diff_span(const uint8_t *cells,
                        size_t len,
                        size_t step_count,
                        size_t *first,
                        size_t *last) {
    size_t count = 0;

    *first = len;
    *last = 0;

    for (size_t i = 0; i < len; i++) {
        if (cells[i] != ether_cell_at_step(i, step_count)) {
            if (count == 0) *first = i;
            *last = i;
            count++;
        }
    }

    return count;
}

static void assert_slice_equals(const uint8_t *cells,
                                size_t pos,
                                const uint8_t *expected,
                                size_t expected_len) {
    for (size_t i = 0; i < expected_len; i++) {
        assert(cells[pos + i] == expected[i]);
    }
}

static void test_glider_A_phase_orbit(void) {
    const size_t phase_len = sizeof(GLIDER_A_F1_1);
    uint8_t cells[sizeof(GLIDER_A_F1_1)];

    memcpy(cells, GLIDER_A_F1_1, phase_len);
    assert_slice_equals(cells, 0, GLIDER_A_F1_1, phase_len);

    periodic_step(cells, phase_len);
    assert_slice_equals(cells, 0, GLIDER_A_F1_1_STEP_1, phase_len);

    periodic_step(cells, phase_len);
    assert_slice_equals(cells, 0, GLIDER_A_F1_1_STEP_2, phase_len);

    periodic_step(cells, phase_len);
    assert_slice_equals(cells, 0, GLIDER_A_F1_1_STEP_3, phase_len);

    for (size_t i = 0; i < phase_len; i++) {
        assert(cells[i] == GLIDER_A_F1_1[(i + 4) % phase_len]);
    }

    printf("  glider_A_phase_orbit: PASS\n");
}

static void test_glider_A_emits_documented_phase(void) {
    const size_t period_count = 8;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 42;
    uint8_t cells[COOK_ETHER_WIDTH * 8];

    cook_ether_emit(cells, period_count);
    cook_glider_A_emit(cells, pos, len);

    assert_slice_equals(cells, pos, GLIDER_A_F1_1, sizeof(GLIDER_A_F1_1));

    printf("  glider_A_emits_documented_phase: PASS\n");
}

static void test_glider_A_emerges(void) {
    const size_t period_count = 36;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 252;
    uint8_t *cells = (uint8_t *)malloc(len);
    size_t first0 = 0;
    size_t last0 = 0;
    size_t first100 = 0;
    size_t last100 = 0;
    size_t count0 = 0;
    size_t count100 = 0;

    assert(cells != NULL);
    cook_ether_emit(cells, period_count);
    cook_glider_A_emit(cells, pos, len);

    count0 = diff_span(cells, len, 0, &first0, &last0);
    assert(count0 > 0);
    assert(first0 >= pos);
    assert(last0 < pos + sizeof(GLIDER_A_F1_1));

    r110_run_n_steps(cells, len, 100);
    count100 = diff_span(cells, len, 100, &first100, &last100);

    assert(count100 > 0);
    assert(first100 != first0 || last100 != last0);
    assert(first100 < first0);

    free(cells);
    printf("  glider_A_emerges: PASS\n");
}

static void test_ether_remains_outside_glider(void) {
    const size_t period_count = 36;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 252;
    uint8_t *cells = (uint8_t *)malloc(len);

    assert(cells != NULL);
    cook_ether_emit(cells, period_count);
    cook_glider_A_emit(cells, pos, len);
    r110_run_n_steps(cells, len, 100);

    for (size_t i = 150; i < 185; i++) {
        assert(cells[i] == ether_cell_at_step(i, 100));
    }
    for (size_t i = 430; i < 470; i++) {
        assert(cells[i] == ether_cell_at_step(i, 100));
    }

    free(cells);
    printf("  ether_remains_outside_glider: PASS\n");
}

int main(void) {
    printf("== test_cook_glider_A ==\n");
    test_glider_A_phase_orbit();
    test_glider_A_emits_documented_phase();
    test_glider_A_emerges();
    test_ether_remains_outside_glider();
    printf("ALL test_cook_glider_A tests passed\n");
    return 0;
}
