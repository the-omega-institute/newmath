#include "cook_construction.h"
#include "cook_data_block.h"
#include "cook_encode.h"
#include "cook_leader.h"
#include "cook_ossifier.h"
#include "rule110.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define ONE_LEADER_POS 100
#define ONE_OSSIFIER_POS 300
#define ONE_DATA_BLOCK_POS 800
#define ONE_EVOLUTION_STEPS 1000

static uint8_t ether_cell_at_step(size_t pos, size_t step_count) {
    size_t shift = (4 * step_count) % COOK_ETHER_WIDTH;

    return COOK_ETHER_PATTERN[(pos + shift) % COOK_ETHER_WIDTH];
}

static size_t count_different(const uint8_t *left,
                              const uint8_t *right,
                              size_t lo,
                              size_t hi) {
    size_t count = 0;

    for (size_t i = lo; i < hi; i++) {
        if (left[i] != right[i]) count++;
    }

    return count;
}

static void assert_ether_range(const uint8_t *cells,
                               size_t lo,
                               size_t hi) {
    for (size_t i = lo; i < hi; i++) {
        assert(cells[i] == COOK_ETHER_PATTERN[i % COOK_ETHER_WIDTH]);
    }
}

static void assert_region_persists(const uint8_t *cells,
                                   size_t len,
                                   size_t center,
                                   size_t radius) {
    size_t lo = center > radius ? center - radius : 0;
    size_t hi = center + radius;
    size_t changed = 0;

    if (hi > len) hi = len;

    for (size_t i = lo; i < hi; i++) {
        if (cells[i] != ether_cell_at_step(i, ONE_EVOLUTION_STEPS)) {
            changed++;
        }
    }

    assert(changed > 0);
}

static void test_one_production_empty_tape(void) {
    uint8_t production[2] = {1, 0};
    uint8_t *productions[1] = {production};
    size_t prod_lens[1] = {2};
    CyclicTagInput ct = {productions, prod_lens, 1, NULL, 0};
    uint8_t *cells = (uint8_t *)malloc(4096);
    uint8_t *ether = (uint8_t *)malloc(4096);
    const size_t ossifier_width = 2 * COOK_OSSIFIER_WIDTH_PER_BIT;
    size_t written = 0;

    assert(cells != NULL);
    assert(ether != NULL);

    written = cook_encode(&ct, cells, 4096);
    assert(written >= 3080);
    assert(written <= 4096);

    cook_ether_emit(ether, written / COOK_ETHER_WIDTH);
    assert(count_different(cells, ether,
                           ONE_LEADER_POS,
                           ONE_LEADER_POS + COOK_LEADER_WIDTH) > 0);
    assert(count_different(cells, ether,
                           ONE_OSSIFIER_POS,
                           ONE_OSSIFIER_POS + ossifier_width) > 0);
    assert_ether_range(cells,
                       ONE_OSSIFIER_POS + ossifier_width,
                       ONE_DATA_BLOCK_POS);

    r110_run_n_steps(cells, written, ONE_EVOLUTION_STEPS);

    assert_region_persists(cells, written, ONE_LEADER_POS, 220);
    assert_region_persists(cells, written, ONE_OSSIFIER_POS, 220);

    free(ether);
    free(cells);
    printf("  one_production_empty_tape: PASS\n");
}

static void test_one_production_three_bit_tape(void) {
    uint8_t production[3] = {1, 1, 0};
    uint8_t *productions[1] = {production};
    size_t prod_lens[1] = {3};
    uint8_t tape[3] = {1, 0, 1};
    CyclicTagInput ct = {productions, prod_lens, 1, tape, 3};
    uint8_t *cells = (uint8_t *)malloc(4096);
    uint8_t *ether = (uint8_t *)malloc(4096);
    const size_t ossifier_width = 3 * COOK_OSSIFIER_WIDTH_PER_BIT;
    const size_t data_width = 3 * COOK_DATA_BLOCK_WIDTH_PER_BIT;
    size_t written = 0;

    assert(cells != NULL);
    assert(ether != NULL);

    written = cook_encode(&ct, cells, 4096);
    assert(written >= 3080);
    assert(written <= 4096);

    cook_ether_emit(ether, written / COOK_ETHER_WIDTH);
    assert(count_different(cells, ether,
                           ONE_LEADER_POS,
                           ONE_LEADER_POS + COOK_LEADER_WIDTH) > 0);
    assert(count_different(cells, ether,
                           ONE_OSSIFIER_POS,
                           ONE_OSSIFIER_POS + ossifier_width) > 0);
    assert(count_different(cells, ether,
                           ONE_DATA_BLOCK_POS,
                           ONE_DATA_BLOCK_POS + data_width) > 0);
    assert_ether_range(cells,
                       ONE_LEADER_POS + COOK_LEADER_WIDTH,
                       ONE_OSSIFIER_POS);
    assert_ether_range(cells,
                       ONE_OSSIFIER_POS + ossifier_width,
                       ONE_DATA_BLOCK_POS);
    assert_ether_range(cells,
                       ONE_DATA_BLOCK_POS + data_width,
                       written);

    r110_run_n_steps(cells, written, ONE_EVOLUTION_STEPS);

    assert_region_persists(cells, written, ONE_LEADER_POS, 220);
    assert_region_persists(cells, written, ONE_OSSIFIER_POS, 220);
    assert_region_persists(cells, written, ONE_DATA_BLOCK_POS, 260);

    free(ether);
    free(cells);
    printf("  one_production_three_bit_tape: PASS\n");
}

int main(void) {
    printf("== test_cook_encode_one ==\n");
    test_one_production_empty_tape();
    test_one_production_three_bit_tape();
    printf("ALL test_cook_encode_one tests passed\n");
    return 0;
}
