#include "cook_construction.h"
#include "cook_data_block.h"
#include "cook_decode.h"
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

static void assert_decodes_after_steps(const CyclicTagInput *ct,
                                       size_t steps,
                                       const char *expected) {
    uint8_t placeholder = 0;
    uint8_t *cells = NULL;
    char decoded[256];
    size_t written = 0;
    int rc = 0;

    rc = cook_encode_phase_exact(ct, &placeholder, 0, &written);
    assert(rc == COOK_ENCODE_PHASE_EXACT_INSUFFICIENT_BUFFER);
    assert(written > 0);

    cells = (uint8_t *)malloc(written);
    assert(cells != NULL);
    rc = cook_encode_phase_exact(ct, cells, written, &written);
    assert(rc == COOK_ENCODE_PHASE_EXACT_OK);

    r110_run_n_steps(cells, written, steps);
    rc = cook_decode_output(cells, written, decoded, sizeof(decoded));
    assert(rc == COOK_DECODE_OK);
    assert(strcmp(decoded, expected) == 0);

    free(cells);
}

static void test_manual_packet_layout_survives_512_steps(void) {
    const size_t periods = 820;
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

    rc = cook_ossifier_emit_phase_exact_branch(cells,
                                               ossifier_pos,
                                               len,
                                               production,
                                               1,
                                               OSSIFIER_AFTER_MOVING_DATA,
                                               OSSIFY_PRODUCE_C2);
    assert(rc == COOK_OSSIFIER_PHASE_EXACT_OK);
    rc = cook_data_block_emit_phase_exact(cells, data_pos, len, tape_y, 1);
    assert(rc == COOK_DATA_BLOCK_PHASE_EXACT_OK);
    rc = cook_leader_emit_phase_exact(cells, leader_pos, len);
    assert(rc == COOK_LEADER_PHASE_EXACT_OK);
    rc = cook_data_block_emit_phase_exact(cells, 8400, len, tape_y, 1);
    assert(rc == COOK_DATA_BLOCK_PHASE_EXACT_OK);

    assert(count_diff_from_ether(cells, ossifier_pos, ossifier_pos + 260, 0) >
           0);
    assert(count_diff_from_ether(cells, data_pos, data_pos + 900, 0) > 0);
    assert(count_diff_from_ether(cells, leader_pos, leader_pos + 730, 0) > 0);

    r110_run_n_steps(cells, len, 512);

    assert(count_diff_from_ether(cells, ossifier_pos - 120,
                                 ossifier_pos + 360, 512) > 0);
    assert(count_diff_from_ether(cells, data_pos - 120,
                                 data_pos + 980, 512) > 0);
    assert(count_diff_from_ether(cells, leader_pos - 120,
                                 leader_pos + 820, 512) > 0);
    assert_ether_range_at_step(cells, 220, 360, 512);

    free(cells);
    printf("  manual_packet_layout_survives_512_steps: PASS\n");
}

static void test_cook_encode_phase_exact_first_pass(void) {
    uint8_t production[1] = {1};
    uint8_t *productions[1] = {production};
    size_t prod_lens[1] = {1};
    uint8_t tape[1] = {1};
    CyclicTagInput ct = {productions, prod_lens, 1, tape, 1};
    uint8_t placeholder = 0;
    uint8_t *cells = NULL;
    size_t written = 0;
    int rc = 0;

    rc = cook_encode_phase_exact(&ct, &placeholder, 0, &written);
    assert(rc == COOK_ENCODE_PHASE_EXACT_INSUFFICIENT_BUFFER);
    cells = (uint8_t *)malloc(written);
    assert(cells != NULL);
    memset(cells, 0x5a, written);
    rc = cook_encode_phase_exact(&ct, cells, written, &written);

    assert(rc == COOK_ENCODE_PHASE_EXACT_OK);
    assert(written > 0);
    assert(count_diff_from_ether(cells, 896, 1600, 0) > 0);
    assert(count_diff_from_ether(cells, 2030, 2260, 0) > 0);
    assert(count_diff_from_ether(cells, 3374, 4240, 0) > 0);

    r110_run_n_steps(cells, written, 100);
    assert_ether_range_at_step(cells, 220, 360, 100);

    free(cells);
    printf("  cook_encode_phase_exact_first_pass: PASS\n");
}

static void test_single_production_round_trip_512(void) {
    uint8_t production[1] = {1};
    uint8_t *productions[1] = {production};
    size_t prod_lens[1] = {1};
    uint8_t tape[1] = {1};
    CyclicTagInput ct = {productions, prod_lens, 1, tape, 1};

    assert_decodes_after_steps(&ct, 512, "Y");

    printf("  single_production_round_trip_512: PASS\n");
}

static void test_two_productions_round_trip_1024(void) {
    uint8_t production0[2] = {1, 0};
    uint8_t production1[1] = {1};
    uint8_t *productions[2] = {production0, production1};
    size_t prod_lens[2] = {2, 1};
    uint8_t tape[2] = {1, 0};
    CyclicTagInput ct = {productions, prod_lens, 2, tape, 2};

    assert_decodes_after_steps(&ct, 1024, "YN");

    printf("  two_productions_round_trip_1024: PASS\n");
}

int main(void) {
    printf("== test_cook_packet_phase_exact ==\n");
    test_manual_packet_layout_survives_512_steps();
    test_cook_encode_phase_exact_first_pass();
    test_single_production_round_trip_512();
    test_two_productions_round_trip_1024();
    printf("ALL test_cook_packet_phase_exact tests passed\n");
    return 0;
}
