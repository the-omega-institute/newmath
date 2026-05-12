#include "cook_construction.h"
#include "rule110.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

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
    assert(last0 < pos + 4);

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
    test_glider_A_emerges();
    test_ether_remains_outside_glider();
    printf("ALL test_cook_glider_A tests passed\n");
    return 0;
}
