#include "cook_construction.h"
#include "cook_data_block.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PHASE_C2_LEN 17
#define PHASE_SYMBOL_STRIDE 867

static void assert_ether_range(const uint8_t *cells, size_t start, size_t end) {
    for (size_t i = start; i < end; i++) {
        assert(cells[i] == COOK_ETHER_PATTERN[i % COOK_ETHER_WIDTH]);
    }
}

static void assert_bits_at(const uint8_t *cells,
                           size_t pos,
                           const char *bits) {
    for (size_t i = 0; bits[i] != '\0'; i++) {
        assert(cells[pos + i] == (uint8_t)(bits[i] == '1' ? 1 : 0));
    }
}

static void assert_c2_symbol(const uint8_t *cells,
                             size_t pos,
                             const int spacings[3]) {
    static const char C2_A_PHASE_1[] = "11111000000100110";
    size_t cursor = pos;

    for (size_t i = 0; i < 4; i++) {
        assert_bits_at(cells, cursor, C2_A_PHASE_1);
        if (i + 1 < 4) {
            cursor += PHASE_C2_LEN +
                ((size_t)spacings[i] * (size_t)COOK_ETHER_WIDTH);
        }
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

static void test_data_block_phase_exact_emits_y_and_n(void) {
    uint8_t cells[4096];
    uint8_t ether[4096];
    const uint8_t y[1] = {1};
    const uint8_t n[1] = {0};
    int rc = 0;
    int y_changed = 0;
    int n_changed = 0;

    cook_ether_emit(cells, sizeof(cells) / COOK_ETHER_WIDTH);
    memcpy(ether, cells, sizeof(cells));

    rc = cook_data_block_emit_phase_exact(cells, 280, sizeof(cells), y, 1);
    assert(rc == COOK_DATA_BLOCK_PHASE_EXACT_OK);
    rc = cook_data_block_emit_phase_exact(cells, 1680, sizeof(cells), n, 1);
    assert(rc == COOK_DATA_BLOCK_PHASE_EXACT_OK);

    for (size_t i = 280; i < 1147; i++) {
        if (cells[i] != ether[i]) y_changed = 1;
    }
    for (size_t i = 1680; i < sizeof(cells); i++) {
        if (cells[i] != ether[i]) n_changed = 1;
    }
    assert(y_changed);
    assert(n_changed);
    assert_ether_range(cells, 0, 280);

    printf("  data_block_phase_exact_emits_y_and_n: PASS\n");
}

static void test_data_block_phase_exact_emits_full_tape(void) {
    uint8_t cells[4096];
    const uint8_t tape_bits[3] = {1, 0, 1};
    static const int Y_SPACINGS[3] = {18, 18, 14};
    static const int N_SPACINGS[3] = {28, 10, 14};
    int rc = 0;

    cook_ether_emit(cells, sizeof(cells) / COOK_ETHER_WIDTH);

    rc = cook_data_block_emit_phase_exact(cells,
                                          280,
                                          sizeof(cells),
                                          tape_bits,
                                          3);

    assert(rc == COOK_DATA_BLOCK_PHASE_EXACT_OK);
    assert_c2_symbol(cells, 280, Y_SPACINGS);
    assert_c2_symbol(cells, 280 + PHASE_SYMBOL_STRIDE, N_SPACINGS);
    assert_c2_symbol(cells, 280 + (2 * PHASE_SYMBOL_STRIDE), Y_SPACINGS);

    printf("  data_block_phase_exact_emits_full_tape: PASS\n");
}

static void test_data_block_phase_exact_unwritable_buffer(void) {
    uint8_t cells[160];
    uint8_t before[160];
    const uint8_t tape_bits[4] = {1, 0, 0, 1};
    int rc = 0;

    memset(cells, 0x5a, sizeof(cells));
    memcpy(before, cells, sizeof(cells));

    rc = cook_data_block_emit_phase_exact(cells, 30, sizeof(cells),
                                          tape_bits, 4);

    assert(rc == COOK_DATA_BLOCK_PHASE_EXACT_CATALOG_MISSING);
    assert(memcmp(cells, before, sizeof(cells)) == 0);

    printf("  data_block_phase_exact_unwritable_buffer: PASS\n");
}

int main(void) {
    printf("== test_cook_data_block ==\n");
    test_data_block_5bit_tape();
    test_data_block_empty();
    test_data_block_phase_exact_emits_y_and_n();
    test_data_block_phase_exact_emits_full_tape();
    test_data_block_phase_exact_unwritable_buffer();
    printf("ALL test_cook_data_block tests passed\n");
    return 0;
}
