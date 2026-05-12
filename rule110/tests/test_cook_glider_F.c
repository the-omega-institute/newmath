#include "cook_construction.h"
#include "cook_glider_F.h"
#include "rule110.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint8_t ether_cell_at_step(size_t pos, size_t step_count) {
    size_t shift = (4 * step_count) % COOK_ETHER_WIDTH;
    return COOK_ETHER_PATTERN[(pos + shift) % COOK_ETHER_WIDTH];
}

static size_t diff_span_range(const uint8_t *cells,
                              size_t lo,
                              size_t hi,
                              size_t step_count,
                              size_t *first,
                              size_t *last) {
    size_t count = 0;

    *first = hi;
    *last = lo;

    for (size_t i = lo; i < hi; i++) {
        if (cells[i] != ether_cell_at_step(i, step_count)) {
            if (count == 0) *first = i;
            *last = i;
            count++;
        }
    }

    return count;
}

static void test_glider_F_moves(void) {
    const size_t period_count = 120;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 840;
    uint8_t *cells = (uint8_t *)malloc(len);
    size_t first0 = 0;
    size_t last0 = 0;
    size_t first100 = 0;
    size_t last100 = 0;
    size_t count0 = 0;
    size_t count100 = 0;

    assert(cells != NULL);
    cook_ether_emit(cells, period_count);
    cook_glider_F_emit(cells, pos, len);

    count0 = diff_span_range(cells, pos - 40, pos + COOK_GLIDER_F_WIDTH + 40,
                             0, &first0, &last0);
    assert(count0 > 0);
    assert(first0 >= pos);
    assert(last0 < pos + COOK_GLIDER_F_WIDTH);

    r110_run_n_steps(cells, len, 100);
    count100 = diff_span_range(cells, pos - 220, pos + 260, 100,
                               &first100, &last100);

    assert(count100 > 0);
    assert(first100 != first0 || last100 != last0);
    assert(first100 < first0);

    free(cells);
    printf("  glider_F_moves: PASS\n");
}

static void test_glider_F_ether_unaffected(void) {
    const size_t period_count = 120;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 840;
    uint8_t *cells = (uint8_t *)malloc(len);

    assert(cells != NULL);
    cook_ether_emit(cells, period_count);
    cook_glider_F_emit(cells, pos, len);
    r110_run_n_steps(cells, len, 100);

    for (size_t i = 260; i < 320; i++) {
        assert(cells[i] == ether_cell_at_step(i, 100));
    }
    for (size_t i = 1340; i < 1400; i++) {
        assert(cells[i] == ether_cell_at_step(i, 100));
    }

    free(cells);
    printf("  glider_F_ether_unaffected: PASS\n");
}

int main(void) {
    printf("== test_cook_glider_F ==\n");
    test_glider_F_moves();
    test_glider_F_ether_unaffected();
    printf("ALL test_cook_glider_F tests passed\n");
    return 0;
}
