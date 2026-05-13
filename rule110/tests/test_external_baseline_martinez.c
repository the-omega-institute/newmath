#include "rule110.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

/* Martinez 2007 page 17 Section 5: e(f1 1) through e(f1 4). */
static const char *MARTINEZ_ETHER_F1_1 = "11111000100110";
static const char *MARTINEZ_ETHER_F1_2 = "10001001101111";
static const char *MARTINEZ_ETHER_F1_3 = "10011011111000";
static const char *MARTINEZ_ETHER_F1_4 = "10111110001001";

/* Martinez 2007 page 5 Table 2 and page 29 Appendix A.2: A glider. */
static const char *MARTINEZ_A_F1_1 = "111110";
static const char *MARTINEZ_A_AFTER_PERIOD = "101111";

/* Martinez 2007 page 5 Table 2 and page 29 Appendix A.3: B glider. */
static const char *MARTINEZ_B_F1_1 = "11111010";
static const char *MARTINEZ_B_AFTER_PERIOD = "11101011";

static void fail_case(const char *name, const char *got, const char *want) {
    printf("FAIL %s: got=%s want=%s\n", name, got, want);
    exit(1);
}

static void bits_repeat_from_str(const char *pattern,
                                 uint8_t *cells,
                                 size_t pattern_width,
                                 size_t repeat_count) {
    size_t r;
    size_t i;

    for (r = 0; r < repeat_count; r++) {
        for (i = 0; i < pattern_width; i++) {
            cells[r * pattern_width + i] = (uint8_t)(pattern[i] == '1');
        }
    }
}

static void bits_to_str_window(const uint8_t *cells,
                               size_t start,
                               size_t width,
                               char *out) {
    size_t i;

    for (i = 0; i < width; i++) out[i] = cells[start + i] ? '1' : '0';
    out[width] = '\0';
}

static void assert_periodic_center_after(const char *name,
                                         const char *initial,
                                         size_t steps,
                                         const char *expected) {
    enum { REPEAT_COUNT = 17, CENTER_REPEAT = 8 };
    uint8_t cells[512];
    char produced[128];
    size_t width = strlen(initial);
    size_t row_width = width * REPEAT_COUNT;
    size_t center_start = width * CENTER_REPEAT;

    if (row_width > sizeof(cells) || width + 1 > sizeof(produced)) {
        printf("FAIL %s: test buffer too small\n", name);
        exit(1);
    }

    bits_repeat_from_str(initial, cells, width, REPEAT_COUNT);
    r110_run_n_steps(cells, row_width, steps);
    bits_to_str_window(cells, center_start, width, produced);

    if (strcmp(produced, expected) != 0) fail_case(name, produced, expected);
}

static void test_martinez_ether_phases(void) {
    assert_periodic_center_after("martinez_ether_f1_1_to_f1_2",
                                 MARTINEZ_ETHER_F1_1,
                                 1,
                                 MARTINEZ_ETHER_F1_2);
    assert_periodic_center_after("martinez_ether_f1_1_to_f1_3",
                                 MARTINEZ_ETHER_F1_1,
                                 2,
                                 MARTINEZ_ETHER_F1_3);
    assert_periodic_center_after("martinez_ether_f1_1_to_f1_4",
                                 MARTINEZ_ETHER_F1_1,
                                 3,
                                 MARTINEZ_ETHER_F1_4);
    assert_periodic_center_after("martinez_ether_period_7",
                                 MARTINEZ_ETHER_F1_1,
                                 7,
                                 MARTINEZ_ETHER_F1_1);
    printf("  martinez_ether_phases: PASS\n");
}

static void test_martinez_a_period_shift(void) {
    assert_periodic_center_after("martinez_A_period_3_shift_2",
                                 MARTINEZ_A_F1_1,
                                 3,
                                 MARTINEZ_A_AFTER_PERIOD);
    printf("  martinez_A_period_shift: PASS\n");
}

static void test_martinez_b_period_shift(void) {
    assert_periodic_center_after("martinez_B_period_4_shift_minus_2",
                                 MARTINEZ_B_F1_1,
                                 4,
                                 MARTINEZ_B_AFTER_PERIOD);
    printf("  martinez_B_period_shift: PASS\n");
}

int main(void) {
    test_martinez_ether_phases();
    test_martinez_a_period_shift();
    test_martinez_b_period_shift();
    return 0;
}
