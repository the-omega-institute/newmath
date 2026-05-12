#include "cook_construction.h"
#include "rule110.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void assert_ether_phase(const uint8_t *cells,
                               size_t start,
                               size_t end,
                               size_t step_count) {
    size_t shift = (4 * step_count) % COOK_ETHER_WIDTH;

    for (size_t i = start; i < end; i++) {
        assert(cells[i] == COOK_ETHER_PATTERN[(i + shift) % COOK_ETHER_WIDTH]);
    }
}

static void test_ether_stable_under_rule110(void) {
    const size_t period_count = 30;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    uint8_t *cells = (uint8_t *)malloc(len);
    assert(cells != NULL);

    cook_ether_emit(cells, period_count);

    for (size_t step = 1; step <= 100; step++) {
        r110_run_n_steps(cells, len, 1);

        if (step % COOK_ETHER_PERIOD == 0) {
            /*
               The finite evaluator uses fixed zero boundaries, so the
               boundary light cone is excluded. Direct evolution of
               00010011011111 shows a +4 mod 14 phase shift per timestep;
               after 7 timesteps it returns to the same cell phase.
            */
            assert_ether_phase(cells, step + 1, len - step - 1, step);
        }
    }

    free(cells);
    printf("  ether_stable_under_rule110: PASS\n");
}

static void test_ether_emit_correct_length(void) {
    const size_t period_count = 10;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    uint8_t out[COOK_ETHER_WIDTH * 10];

    memset(out, 0, sizeof(out));
    cook_ether_emit(out, period_count);

    for (size_t i = 0; i < len; i++) {
        assert(out[i] == COOK_ETHER_PATTERN[i % COOK_ETHER_WIDTH]);
    }

    printf("  ether_emit_correct_length: PASS\n");
}

int main(void) {
    printf("== test_cook_ether ==\n");
    test_ether_stable_under_rule110();
    test_ether_emit_correct_length();
    printf("ALL test_cook_ether tests passed\n");
    return 0;
}
