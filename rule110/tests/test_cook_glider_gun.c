#include "cook_construction.h"
#include "cook_glider_gun.h"
#include "rule110.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint8_t ether_cell_at_step(size_t pos, size_t step_count) {
    size_t shift = (4 * step_count) % COOK_ETHER_WIDTH;
    return COOK_ETHER_PATTERN[(pos + shift) % COOK_ETHER_WIDTH];
}

static size_t diff_cluster_count(const uint8_t *cells,
                                 size_t lo,
                                 size_t hi,
                                 size_t step_count) {
    size_t clusters = 0;
    size_t run_len = 0;
    size_t gap_len = 64;

    for (size_t i = lo; i < hi; i++) {
        if (cells[i] != ether_cell_at_step(i, step_count)) {
            if (run_len == 0 && gap_len >= 6) clusters++;
            run_len++;
            gap_len = 0;
        } else {
            run_len = 0;
            if (gap_len < 64) gap_len++;
        }
    }

    return clusters;
}

static void test_glider_gun_emits_periodically(void) {
    const size_t period_count = 320;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 2240;
    uint8_t *cells = (uint8_t *)malloc(len);
    size_t clusters = 0;

    assert(cells != NULL);
    cook_ether_emit(cells, period_count);
    cook_glider_gun_emit(cells, pos, len);

    r110_run_n_steps(cells, len, 500);
    clusters = diff_cluster_count(cells, pos - 900, pos + 1100, 500);

    assert(clusters > 1);

    free(cells);
    printf("  glider_gun_emits_periodically: PASS\n");
}

static void test_glider_gun_ether_unaffected(void) {
    const size_t period_count = 320;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 2240;
    uint8_t *cells = (uint8_t *)malloc(len);

    assert(cells != NULL);
    cook_ether_emit(cells, period_count);
    cook_glider_gun_emit(cells, pos, len);
    r110_run_n_steps(cells, len, 500);

    for (size_t i = 260; i < 340; i++) {
        assert(cells[i] == ether_cell_at_step(i, 500));
    }
    for (size_t i = 3920; i < 4000; i++) {
        assert(cells[i] == ether_cell_at_step(i, 500));
    }

    free(cells);
    printf("  glider_gun_ether_unaffected: PASS\n");
}

int main(void) {
    printf("== test_cook_glider_gun ==\n");
    test_glider_gun_emits_periodically();
    test_glider_gun_ether_unaffected();
    printf("ALL test_cook_glider_gun tests passed\n");
    return 0;
}
