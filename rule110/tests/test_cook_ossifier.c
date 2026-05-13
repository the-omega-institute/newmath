#include "cook_construction.h"
#include "cook_ossifier.h"
#include "rule110.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define PHASE_A_LEN 6

static void assert_bits_at(const uint8_t *cells,
                           size_t pos,
                           const char *bits) {
    for (size_t i = 0; bits[i] != '\0'; i++) {
        assert(cells[pos + i] == (uint8_t)(bits[i] == '1' ? 1 : 0));
    }
}

static void assert_a4_group_at(const uint8_t *cells, size_t pos) {
    static const char A_PHASE_1[] = "111110";

    for (size_t i = 0; i < 4; i++) {
        assert_bits_at(cells, pos + (i * PHASE_A_LEN), A_PHASE_1);
    }
}

static uint8_t ether_cell_at_step(size_t pos, size_t step_count) {
    size_t shift = (4 * step_count) % COOK_ETHER_WIDTH;
    return COOK_ETHER_PATTERN[(pos + shift) % COOK_ETHER_WIDTH];
}

static size_t perturbation_span(const uint8_t *cells,
                                size_t lo,
                                size_t hi,
                                size_t *first_out,
                                size_t *last_out) {
    size_t count = 0;
    size_t first = hi;
    size_t last = lo;

    for (size_t i = lo; i < hi; i++) {
        if (cells[i] != COOK_ETHER_PATTERN[i % COOK_ETHER_WIDTH]) {
            if (count == 0) first = i;
            last = i;
            count++;
        }
    }

    *first_out = first;
    *last_out = last;
    return count;
}

static void test_ossifier_3bit_production(void) {
    const size_t period_count = 96;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    const size_t pos = 560;
    const uint8_t production[3] = {1, 0, 1};
    const size_t expected_width = 3 * COOK_OSSIFIER_WIDTH_PER_BIT;
    uint8_t *cells = (uint8_t *)malloc(len);
    size_t first = 0;
    size_t last = 0;
    size_t changed = 0;
    size_t still_perturbed = 0;

    assert(cells != NULL);
    cook_ether_emit(cells, period_count);
    cook_ossifier_emit(cells, pos, len, production, 3);

    changed = perturbation_span(cells, pos, pos + expected_width,
                                &first, &last);
    assert(changed > 0);
    assert(first == pos);
    assert(last == pos + expected_width - 1);

    for (size_t i = 40; i < pos; i++) {
        assert(cells[i] == COOK_ETHER_PATTERN[i % COOK_ETHER_WIDTH]);
    }
    for (size_t i = pos + expected_width; i < len - 40; i++) {
        assert(cells[i] == COOK_ETHER_PATTERN[i % COOK_ETHER_WIDTH]);
    }

    r110_run_n_steps(cells, len, 200);

    for (size_t i = pos; i < pos + expected_width; i++) {
        if (cells[i] != ether_cell_at_step(i, 200)) still_perturbed++;
    }
    assert(still_perturbed > 0);

    free(cells);
    printf("  ossifier_3bit_production: PASS\n");
}

static void test_ossifier_empty_production(void) {
    const size_t period_count = 24;
    const size_t len = COOK_ETHER_WIDTH * period_count;
    uint8_t *cells = (uint8_t *)malloc(len);
    uint8_t *initial = (uint8_t *)malloc(len);
    const uint8_t production[1] = {1};

    assert(cells != NULL);
    assert(initial != NULL);
    cook_ether_emit(cells, period_count);
    memcpy(initial, cells, len);

    cook_ossifier_emit(cells, 70, len, production, 0);

    assert(memcmp(cells, initial, len) == 0);

    free(initial);
    free(cells);
    printf("  ossifier_empty_production: PASS\n");
}

static void test_ossifier_phase_exact_emits_packet(void) {
    uint8_t cells[768];
    uint8_t ether[768];
    const uint8_t production[1] = {1};
    int rc = 0;
    size_t changed = 0;
    size_t first = 0;
    size_t last = 0;

    cook_ether_emit(cells, sizeof(cells) / COOK_ETHER_WIDTH);
    memcpy(ether, cells, sizeof(cells));

    rc = cook_ossifier_emit_phase_exact(cells, 42, sizeof(cells),
                                        production, 1);

    assert(rc == COOK_OSSIFIER_PHASE_EXACT_OK);
    changed = perturbation_span(cells, 42, sizeof(cells), &first, &last);
    assert(changed > 0);
    assert(first >= 42);
    assert(first < 42 + 10);
    assert(last >= 42 + 39);
    assert(memcmp(cells, ether, 42) == 0);
    assert_a4_group_at(cells, 42);
    assert_a4_group_at(cells, 42 + 24 + (11 * COOK_ETHER_WIDTH));
    assert_a4_group_at(cells, 42 + (2 * (24 + (11 * COOK_ETHER_WIDTH))));
    assert_a4_group_at(cells, 42 + (3 * (24 + (11 * COOK_ETHER_WIDTH))));

    printf("  ossifier_phase_exact_emits_packet: PASS\n");
}

static void test_ossifier_phase_exact_unwritable_buffer(void) {
    uint8_t cells[128];
    uint8_t before[128];
    const uint8_t production[3] = {1, 0, 1};
    int rc = 0;

    memset(cells, 0x5a, sizeof(cells));
    memcpy(before, cells, sizeof(cells));

    rc = cook_ossifier_emit_phase_exact(cells, 15, sizeof(cells),
                                        production, 3);

    assert(rc == COOK_OSSIFIER_PHASE_EXACT_CATALOG_MISSING);
    assert(memcmp(cells, before, sizeof(cells)) == 0);

    printf("  ossifier_phase_exact_unwritable_buffer: PASS\n");
}

int main(void) {
    printf("== test_cook_ossifier ==\n");
    test_ossifier_3bit_production();
    test_ossifier_empty_production();
    test_ossifier_phase_exact_emits_packet();
    test_ossifier_phase_exact_unwritable_buffer();
    printf("ALL test_cook_ossifier tests passed\n");
    return 0;
}
