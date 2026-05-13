#include "cook_construction.h"
#include "cook_collision_identity.h"
#include "cook_leader.h"
#include "rule110.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void assert_buffers_differ(const uint8_t *left,
                                  const uint8_t *right,
                                  size_t len) {
    int differs = 0;

    for (size_t i = 0; i < len; i++) {
        if (left[i] != right[i]) differs = 1;
    }

    assert(differs);
}

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

static int differs_from_ether(const uint8_t *cells, size_t start, size_t end) {
    for (size_t i = start; i < end; i++) {
        if (cells[i] != COOK_ETHER_PATTERN[i % COOK_ETHER_WIDTH]) return 1;
    }
    return 0;
}

static size_t count_bits_at(const uint8_t *cells,
                            size_t start,
                            size_t end,
                            const char *bits) {
    size_t count = 0;
    size_t bits_len = strlen(bits);

    if (bits_len == 0 || end < start || end - start < bits_len) return 0;
    for (size_t pos = start; pos + bits_len <= end; pos++) {
        int match = 1;

        for (size_t i = 0; i < bits_len; i++) {
            uint8_t bit = bits[i] == '1' ? 1u : 0u;

            if (cells[pos + i] != bit) match = 0;
        }
        if (match) count++;
    }
    return count;
}

static void test_leader_figure8_alignment(void) {
    int k = -1;
    int alignment = -1;

    assert(cook_leader_prepared_k(LEADER_PREPARED_AFTER_MOVING_DATA,
                                  6u,
                                  &k));
    assert(k == 0);
    assert(cook_leader_prepared_invisible_alignment(
        LEADER_PREPARED_AFTER_MOVING_DATA,
        6u,
        &alignment));
    assert(alignment == 5);
    assert(cook_leader_prepared_k(
        LEADER_PREPARED_AFTER_REJECTED_INVISIBLES,
        6u,
        &k));
    assert(k == 2);
    assert(cook_leader_prepared_invisible_alignment(
        LEADER_PREPARED_AFTER_REJECTED_INVISIBLES,
        6u,
        &alignment));
    assert(alignment == 1);
    assert(!cook_leader_prepared_k(
        LEADER_PREPARED_AFTER_REJECTED_INVISIBLES,
        5u,
        &k));

    printf("  leader_figure8_alignment: PASS\n");
}

static void test_leader_figure11_prepared_placement(void) {
    CookLeaderPreparedPlacement placement;

    assert(cook_leader_prepared_placement(6u, &placement));
    assert(placement.v[0] == 0);
    assert(placement.v[1] == 1);
    assert(placement.w[0] == 2);
    assert(placement.w[1] == 3);
    assert(placement.x[0] == 1);
    assert(placement.x[1] == 0);
    assert(placement.y[0] == 1);
    assert(placement.y[1] == 0);
    assert(placement.y[2] == 3);
    assert(placement.y[3] == 0);
    assert(placement.y[4] == 3);
    assert(placement.y[5] == 0);
    assert(placement.y_repeats == 11u);
    assert(placement.total_mod4 == 1);

    assert(cook_leader_prepared_placement(12u, &placement));
    assert(placement.y_repeats == 23u);
    assert(placement.total_mod4 == 1);
    assert(!cook_leader_prepared_placement(5u, &placement));
    assert(!cook_leader_prepared_placement(0u, &placement));
    assert(!cook_leader_prepared_placement(6u, NULL));

    printf("  leader_figure11_prepared_placement: PASS\n");
}

static void test_leader_figure10_alignment(void) {
    CookLeaderFigure10Alignment alignment;
    const CookFigure10PassThrough *first =
        cook_figure_10_pass_through(COOK_FIGURE10_FIRST_MOVING_AFTER_INVISIBLE);
    const CookFigure10PassThrough *invisible =
        cook_figure_10_pass_through(COOK_FIGURE10_INVISIBLE);
    const CookFigure10PassThrough *moving =
        cook_figure_10_pass_through(COOK_FIGURE10_MOVING_AFTER_MOVING);

    assert(cook_leader_figure10_alignment(&alignment));
    assert(alignment.first_moving_after_invisible == 3);
    assert(alignment.invisible_c2_spacing == 2);
    assert(alignment.moving_after_moving == 3);
    assert(first != NULL);
    assert(first->label_count == 3u);
    assert(first->labels[0] == 0);
    assert(first->labels[1] == 1);
    assert(first->labels[2] == 2);
    assert(invisible != NULL);
    assert(invisible->label_count == 2u);
    assert(invisible->labels[0] == 2);
    assert(invisible->labels[1] == 1);
    assert(moving != NULL);
    assert(moving->label_count == 3u);
    assert(moving->labels[0] == 0);
    assert(moving->labels[1] == 1);
    assert(moving->labels[2] == 2);
    assert(!cook_leader_figure10_alignment(NULL));

    printf("  leader_figure10_alignment: PASS\n");
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

static void test_leader_phase_exact_emits_packet(void) {
    uint8_t cells[2048];
    uint8_t ether[2048];
    int rc = 0;

    cook_ether_emit(cells, sizeof(cells) / COOK_ETHER_WIDTH);
    memcpy(ether, cells, sizeof(cells));

    rc = cook_leader_emit_phase_exact(cells, 154, sizeof(cells));

    assert(rc == COOK_LEADER_PHASE_EXACT_OK);
    assert(differs_from_ether(cells, 154, 858));
    assert(memcmp(cells, ether, 154) == 0);

    printf("  leader_phase_exact_emits_packet: PASS\n");
}

static void test_leader_phase_exact_accept_reject_differ(void) {
    uint8_t accept_cells[2048];
    uint8_t reject_cells[2048];
    int rc = 0;
    size_t accept_a4_count = 0;
    size_t accept_a2_count = 0;
    size_t reject_a3_count = 0;

    cook_ether_emit(accept_cells, sizeof(accept_cells) / COOK_ETHER_WIDTH);
    memcpy(reject_cells, accept_cells, sizeof(accept_cells));

    rc = cook_leader_emit_phase_exact_accept(accept_cells,
                                             154,
                                             sizeof(accept_cells));
    assert(rc == COOK_LEADER_PHASE_EXACT_OK);
    rc = cook_leader_emit_phase_exact_reject(reject_cells,
                                             154,
                                             sizeof(reject_cells));
    assert(rc == COOK_LEADER_PHASE_EXACT_OK);

    assert(differs_from_ether(accept_cells, 154, 1100));
    assert(differs_from_ether(reject_cells, 154, 1100));
    assert_buffers_differ(accept_cells + 154, reject_cells + 154, 946);
    accept_a4_count = count_bits_at(accept_cells, 858, 1280, "111110");
    accept_a2_count = count_bits_at(accept_cells,
                                    858,
                                    1280,
                                    "11111000111000100110");
    reject_a3_count = count_bits_at(reject_cells,
                                    880,
                                    1280,
                                    "11111000100110100110");
    assert(accept_a4_count >= 1);
    assert(accept_a2_count == 0);
    assert(reject_a3_count >= 1);

    printf("  leader_phase_exact_accept_reject_differ: PASS\n");
}

static void test_leader_phase_exact_short_leader_offset(void) {
    uint8_t regular_cells[2048];
    uint8_t short_cells[2048];
    int rc = 0;

    cook_ether_emit(regular_cells, sizeof(regular_cells) / COOK_ETHER_WIDTH);
    memcpy(short_cells, regular_cells, sizeof(regular_cells));

    rc = cook_leader_emit_phase_exact_kind(regular_cells,
                                           154,
                                           sizeof(regular_cells),
                                           LEADER_REGULAR);
    assert(rc == COOK_LEADER_PHASE_EXACT_OK);
    rc = cook_leader_emit_phase_exact_kind(short_cells,
                                           154,
                                           sizeof(short_cells),
                                           LEADER_SHORT);
    assert(rc == COOK_LEADER_PHASE_EXACT_OK);

    assert_buffers_differ(regular_cells + 154, short_cells + 154, 1100);
    assert(memcmp(short_cells, regular_cells, 154) == 0);
    assert(differs_from_ether(short_cells,
                              154 + (3 * COOK_ETHER_WIDTH),
                              154 + (3 * COOK_ETHER_WIDTH) + 120));

    printf("  leader_phase_exact_short_leader_offset: PASS\n");
}

static void test_leader_phase_exact_unwritable_buffer(void) {
    uint8_t cells[96];
    uint8_t before[96];
    int rc = 0;

    memset(cells, 0x5a, sizeof(cells));
    memcpy(before, cells, sizeof(cells));

    rc = cook_leader_emit_phase_exact(cells, 20, sizeof(cells));

    assert(rc == COOK_LEADER_PHASE_EXACT_CATALOG_MISSING);
    assert(memcmp(cells, before, sizeof(cells)) == 0);

    printf("  leader_phase_exact_unwritable_buffer: PASS\n");
}

int main(void) {
    printf("== test_cook_leader ==\n");
    test_leader_figure8_alignment();
    test_leader_figure11_prepared_placement();
    test_leader_figure10_alignment();
    test_leader_stable();
    test_leader_does_not_destroy_ether_outside();
    test_leader_phase_exact_emits_packet();
    test_leader_phase_exact_accept_reject_differ();
    test_leader_phase_exact_short_leader_offset();
    test_leader_phase_exact_unwritable_buffer();
    printf("ALL test_cook_leader tests passed\n");
    return 0;
}
