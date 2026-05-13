#include "cook_construction.h"
#include "cook_glider_C.h"
#include "rule110.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint8_t ether_cell_at_step(size_t pos, size_t step_count) {
    size_t shift = (4 * step_count) % COOK_ETHER_WIDTH;
    return COOK_ETHER_PATTERN[(pos + shift) % COOK_ETHER_WIDTH];
}

static void test_glider_C_moves(void) {
    const size_t period_count = 20;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 100;
    uint8_t *cells = (uint8_t *)malloc(len);
    uint8_t *initial = (uint8_t *)malloc(len);
    int changed = 0;
    int perturbed = 0;

    assert(cells != NULL);
    assert(initial != NULL);
    cook_ether_emit(cells, period_count);
    cook_glider_C_emit(cells, pos, len);
    memcpy(initial, cells, len);

    r110_run_n_steps(cells, len, 100);

    for (size_t i = pos - 50; i <= pos + 50; i++) {
        if (cells[i] != initial[i]) changed = 1;
        if (cells[i] != ether_cell_at_step(i, 100)) perturbed = 1;
    }
    assert(changed);
    assert(perturbed);

    for (size_t i = 10; i <= pos - 100; i++) {
        assert(cells[i] == ether_cell_at_step(i, 100));
    }

    free(initial);
    free(cells);
    printf("  glider_C_moves: PASS\n");
}

static void test_glider_C_ether_unaffected(void) {
    const size_t period_count = 20;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 100;
    uint8_t *cells = (uint8_t *)malloc(len);

    assert(cells != NULL);
    cook_ether_emit(cells, period_count);
    cook_glider_C_emit(cells, pos, len);
    r110_run_n_steps(cells, len, 50);

    for (size_t i = pos + COOK_GLIDER_C_WIDTH + 51; i < len - 20; i++) {
        assert(cells[i] == ether_cell_at_step(i, 50));
    }

    free(cells);
    printf("  glider_C_ether_unaffected: PASS\n");
}

int main(void) {
    printf("== test_cook_glider_C ==\n");
    test_glider_C_moves();
    test_glider_C_ether_unaffected();
    printf("ALL test_cook_glider_C tests passed\n");
    return 0;
}
