#include "cook_construction.h"
#include "cook_data_block.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void assert_ether_range(const uint8_t *cells, size_t start, size_t end) {
    for (size_t i = start; i < end; i++) {
        assert(cells[i] == COOK_ETHER_PATTERN[i % COOK_ETHER_WIDTH]);
    }
}

static void test_data_block_5bit_tape(void) {
    const size_t period_count = 40;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 140;
    const uint8_t tape_bits[5] = {1, 0, 1, 1, 0};
    const size_t width = 5 * COOK_DATA_BLOCK_WIDTH_PER_BIT;
    uint8_t *cells = (uint8_t *)malloc(len);
    uint8_t *ether = (uint8_t *)malloc(len);
    size_t first_changed = len;
    size_t last_changed = 0;
    int saw_change = 0;

    assert(cells != NULL);
    assert(ether != NULL);
    cook_ether_emit(cells, period_count);
    memcpy(ether, cells, len);

    cook_data_block_emit(cells, pos, len, tape_bits, 5);

    for (size_t i = 0; i < len; i++) {
        if (cells[i] != ether[i]) {
            if (!saw_change) first_changed = i;
            last_changed = i;
            saw_change = 1;
        }
    }

    assert(saw_change);
    assert(first_changed >= pos);
    assert(last_changed < pos + width);

    for (size_t bit = 0; bit < 5; bit++) {
        int slot_changed = 0;
        size_t slot_start = pos + (bit * COOK_DATA_BLOCK_WIDTH_PER_BIT);
        size_t slot_end = slot_start + COOK_DATA_BLOCK_WIDTH_PER_BIT;

        for (size_t i = slot_start; i < slot_end; i++) {
            if (cells[i] != ether[i]) slot_changed = 1;
        }
        assert(slot_changed);
    }

    assert_ether_range(cells, 0, pos);
    assert_ether_range(cells, pos + width, len);

    free(ether);
    free(cells);
    printf("  data_block_5bit_tape: PASS\n");
}

static void test_data_block_empty(void) {
    const size_t period_count = 12;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    uint8_t cells[COOK_ETHER_WIDTH * 12];
    uint8_t ether[COOK_ETHER_WIDTH * 12];

    cook_ether_emit(cells, period_count);
    memcpy(ether, cells, sizeof(cells));

    cook_data_block_emit(cells, 50, len, NULL, 0);

    for (size_t i = 0; i < len; i++) {
        assert(cells[i] == ether[i]);
    }

    printf("  data_block_empty: PASS\n");
}

int main(void) {
    printf("== test_cook_data_block ==\n");
    test_data_block_5bit_tape();
    test_data_block_empty();
    printf("ALL test_cook_data_block tests passed\n");
    return 0;
}
