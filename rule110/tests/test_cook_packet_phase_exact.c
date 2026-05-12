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

static uint8_t ether_cell_at_step(size_t pos, size_t step_count) {
    size_t shift = (4 * step_count) % COOK_ETHER_WIDTH;
    return COOK_ETHER_PATTERN[(pos + shift) % COOK_ETHER_WIDTH];
}

static size_t count_diff_from_ether(const uint8_t *cells,
                                    size_t start,
                                    size_t end,
                                    size_t step_count) {
    size_t count = 0;

    for (size_t i = start; i < end; i++) {
        if (cells[i] != ether_cell_at_step(i, step_count)) count++;
    }

    return count;
}

static void assert_ether_range_at_step(const uint8_t *cells,
                                       size_t start,
                                       size_t end,
                                       size_t step_count) {
    for (size_t i = start; i < end; i++) {
        assert(cells[i] == ether_cell_at_step(i, step_count));
    }
}

static void test_manual_packet_layout_survives_100_steps(void) {
    const size_t periods = 420;
    const size_t len = periods * COOK_ETHER_WIDTH;
    const size_t ossifier_pos = 560;
    const size_t data_pos = 1680;
    const size_t leader_pos = 3920;
    const uint8_t production[1] = {1};
    const uint8_t tape_y[1] = {1};
    uint8_t *cells = (uint8_t *)malloc(len);
    int rc = 0;

    assert(cells != NULL);
    cook_ether_emit(cells, periods);

    rc = cook_ossifier_emit_phase_exact(cells,
                                        ossifier_pos,
                                        len,
                                        production,
                                        1);
    assert(rc == COOK_OSSIFIER_PHASE_EXACT_OK);
    rc = cook_data_block_emit_phase_exact(cells, data_pos, len, tape_y, 1);
    assert(rc == COOK_DATA_BLOCK_PHASE_EXACT_OK);
    rc = cook_leader_emit_phase_exact(cells, leader_pos, len);
    assert(rc == COOK_LEADER_PHASE_EXACT_OK);

    assert(count_diff_from_ether(cells, ossifier_pos, ossifier_pos + 260, 0) >
           0);
    assert(count_diff_from_ether(cells, data_pos, data_pos + 900, 0) > 0);
    assert(count_diff_from_ether(cells, leader_pos, leader_pos + 730, 0) > 0);

    r110_run_n_steps(cells, len, 100);

    assert(count_diff_from_ether(cells, ossifier_pos - 120,
                                 ossifier_pos + 360, 100) > 0);
    assert(count_diff_from_ether(cells, data_pos - 120,
                                 data_pos + 980, 100) > 0);
    assert(count_diff_from_ether(cells, leader_pos - 120,
                                 leader_pos + 820, 100) > 0);
    assert_ether_range_at_step(cells, 220, 360, 100);
    assert_ether_range_at_step(cells, 3200, 3400, 100);

    free(cells);
    printf("  manual_packet_layout_survives_100_steps: PASS\n");
}

static void test_cook_encode_phase_exact_first_pass(void) {
    uint8_t production[1] = {1};
    uint8_t *productions[1] = {production};
    size_t prod_lens[1] = {1};
    uint8_t tape[1] = {1};
    CyclicTagInput ct = {productions, prod_lens, 1, tape, 1};
    uint8_t cells[8192];
    size_t written = 0;
    int rc = 0;

    memset(cells, 0x5a, sizeof(cells));
    rc = cook_encode_phase_exact(&ct, cells, sizeof(cells), &written);

    assert(rc == COOK_ENCODE_PHASE_EXACT_OK);
    assert(written > 0);
    assert(written <= sizeof(cells));
    assert(count_diff_from_ether(cells, 896, 1600, 0) > 0);
    assert(count_diff_from_ether(cells, 2030, 2260, 0) > 0);
    assert(count_diff_from_ether(cells, 3374, 4240, 0) > 0);

    r110_run_n_steps(cells, written, 100);
    assert_ether_range_at_step(cells, 220, 360, 100);
    assert_ether_range_at_step(cells, written - 700, written - 500, 100);

    printf("  cook_encode_phase_exact_first_pass: PASS\n");
}

int main(void) {
    printf("== test_cook_packet_phase_exact ==\n");
    test_manual_packet_layout_survives_100_steps();
    test_cook_encode_phase_exact_first_pass();
    printf("ALL test_cook_packet_phase_exact tests passed\n");
    return 0;
}
