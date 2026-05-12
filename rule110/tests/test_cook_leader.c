#include "cook_construction.h"
#include "cook_leader.h"
#include "rule110.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static uint8_t ether_cell_at_step(size_t pos, size_t step_count) {
    size_t shift = (4 * step_count) % COOK_ETHER_WIDTH;
    return COOK_ETHER_PATTERN[(pos + shift) % COOK_ETHER_WIDTH];
}

static size_t count_perturbed(const uint8_t *cells,
                              size_t lo,
                              size_t hi,
                              size_t step_count) {
    size_t count = 0;

    for (size_t i = lo; i < hi; i++) {
        if (cells[i] != ether_cell_at_step(i, step_count)) count++;
    }

    return count;
}

static void test_leader_stable(void) {
    const size_t period_count = 260;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 1400;
    uint8_t *cells = (uint8_t *)malloc(len);
    size_t perturbed = 0;

    assert(cells != NULL);
    assert(COOK_LEADER_WIDTH == 20);
    assert(COOK_LEADER_STABILITY_STEPS >= 500);

    cook_ether_emit(cells, period_count);
    cook_leader_emit(cells, pos, len);
    r110_run_n_steps(cells, len, 500);

    perturbed = count_perturbed(cells, pos - 50, pos + 51, 500);
    assert(perturbed > 0);

    free(cells);
    printf("  leader_stable: PASS\n");
}

static void test_leader_does_not_destroy_ether_outside(void) {
    const size_t period_count = 120;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 840;
    uint8_t *cells = (uint8_t *)malloc(len);

    assert(cells != NULL);
    cook_ether_emit(cells, period_count);
    cook_leader_emit(cells, pos, len);
    r110_run_n_steps(cells, len, 100);

    for (size_t i = 220; i < 320; i++) {
        assert(cells[i] == ether_cell_at_step(i, 100));
    }
    for (size_t i = 1360; i < 1460; i++) {
        assert(cells[i] == ether_cell_at_step(i, 100));
    }

    free(cells);
    printf("  leader_does_not_destroy_ether_outside: PASS\n");
}

int main(void) {
    printf("== test_cook_leader ==\n");
    test_leader_stable();
    test_leader_does_not_destroy_ether_outside();
    printf("ALL test_cook_leader tests passed\n");
    return 0;
}
