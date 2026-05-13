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

/* Martinez 2007 Table 2, page 5, lines 184-205: C1 period=7 displacement=0;
   Appendix A.6, page 31, lines 1412-1415: C1(A,f1_1). */
static const char *MARTINEZ_C1_A_F1_1 = "111110000";

/* Martinez 2007 Table 2, page 5, lines 184-205: C2 period=7 displacement=0;
   Appendix A.7, page 31, lines 1423-1426: C2(A,f1_1). */
static const char *MARTINEZ_C2_A_F1_1 = "11111000000100110";

/* Martinez 2007 Table 2, page 5, lines 184-205: Bbar period=12 displacement=-6;
   Appendix A.4, page 30, lines 1375-1378: Bbar(A,f1_1). */
static const char *MARTINEZ_BBAR_A_F1_1 = "1111100010110111100110";

/* Martinez 2007 Table 2, page 5, lines 184-205: E period=15 displacement=-4;
   Appendix A.11, page 32, lines 1482-1485: E(A,f1_1). */
static const char *MARTINEZ_E_A_F1_1 = "1111100000000100110";

/* Martinez 2007 Table 2, page 5, lines 184-205: Ebar period=30 displacement=-8;
   Appendix A.12, page 32, lines 1503-1506: Ebar(A,f1_1). */
static const char *MARTINEZ_EBAR_A_F1_1 = "111110000100011111010";

/* Martinez 2007 Table 2, page 5, lines 184-205: F period=36 displacement=-4;
   Appendix A.13, page 33, lines 1549-1552: F(A,f2_1). */
static const char *MARTINEZ_F_A_F2_1 = "11111000100111111111000100110";

/* Martinez 2007 Table 2, page 5, lines 184-205: G period=42 displacement=-14;
   Appendix A.14, page 34, lines 1604-1607: G(A,f3_1). */
static const char *MARTINEZ_G_A_F3_1 =
    "11111000100110111100111111111000100110";

/* Martinez 2007 Table 2, page 5, lines 184-205: H period=92 displacement=-18;
   Appendix A.15, pages 35-36, lines 1665-1672: H(A,f1_1). */
static const char *MARTINEZ_H_A_F1_1 =
    "11111000101100000000111110001001101001111111000100110";

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

static void assert_periodic_shift_after(const char *name,
                                        const char *initial,
                                        size_t steps,
                                        int displacement) {
    enum { REPEAT_COUNT = 41, CENTER_REPEAT = 20 };
    uint8_t cells[4096];
    uint8_t before[4096];
    char produced[256];
    char expected[256];
    size_t width = strlen(initial);
    size_t row_width = width * REPEAT_COUNT;
    size_t center_start = width * CENTER_REPEAT;
    size_t i;

    if (row_width > sizeof(cells) || width + 1 > sizeof(produced)) {
        printf("FAIL %s: test buffer too small\n", name);
        exit(1);
    }

    bits_repeat_from_str(initial, cells, width, REPEAT_COUNT);
    memcpy(before, cells, row_width);

    r110_run_n_steps(cells, row_width, steps);
    bits_to_str_window(cells, center_start, width, produced);

    for (i = 0; i < width; i++) {
        long src = (long)(center_start + i) - (long)displacement;
        if (src < 0 || src >= (long)row_width) {
            printf("FAIL %s: shifted window outside test row\n", name);
            exit(1);
        }
        expected[i] = before[(size_t)src] ? '1' : '0';
    }
    expected[width] = '\0';

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

static void test_martinez_c1_period_shift(void) {
    assert_periodic_shift_after("martinez_C1_A_period_7_shift_0",
                                MARTINEZ_C1_A_F1_1,
                                7,
                                0);
    printf("  martinez_C1_period_shift: PASS\n");
}

static void test_martinez_c2_period_shift(void) {
    assert_periodic_shift_after("martinez_C2_A_period_7_shift_0",
                                MARTINEZ_C2_A_F1_1,
                                7,
                                0);
    printf("  martinez_C2_period_shift: PASS\n");
}

static void test_martinez_bbar_period_shift(void) {
    assert_periodic_shift_after("martinez_Bbar_A_period_12_shift_minus_6",
                                MARTINEZ_BBAR_A_F1_1,
                                12,
                                -6);
    printf("  martinez_Bbar_period_shift: PASS\n");
}

static void test_martinez_e_period_shift(void) {
    assert_periodic_shift_after("martinez_E_A_period_15_shift_minus_4",
                                MARTINEZ_E_A_F1_1,
                                15,
                                -4);
    printf("  martinez_E_period_shift: PASS\n");
}

static void test_martinez_ebar_period_shift(void) {
    assert_periodic_shift_after("martinez_Ebar_A_period_30_shift_minus_8",
                                MARTINEZ_EBAR_A_F1_1,
                                30,
                                -8);
    printf("  martinez_Ebar_period_shift: PASS\n");
}

static void test_martinez_f_period_shift(void) {
    assert_periodic_shift_after("martinez_F_A_f2_period_36_shift_minus_4",
                                MARTINEZ_F_A_F2_1,
                                36,
                                -4);
    printf("  martinez_F_period_shift: PASS\n");
}

static void test_martinez_g_period_shift(void) {
    assert_periodic_shift_after("martinez_G_A_f3_period_42_shift_minus_14",
                                MARTINEZ_G_A_F3_1,
                                42,
                                -14);
    printf("  martinez_G_period_shift: PASS\n");
}

static void test_martinez_h_period_shift(void) {
    assert_periodic_shift_after("martinez_H_A_period_92_shift_minus_18",
                                MARTINEZ_H_A_F1_1,
                                92,
                                -18);
    printf("  martinez_H_period_shift: PASS\n");
}

int main(void) {
    test_martinez_ether_phases();
    test_martinez_a_period_shift();
    test_martinez_b_period_shift();
    test_martinez_c1_period_shift();
    test_martinez_c2_period_shift();
    test_martinez_bbar_period_shift();
    test_martinez_e_period_shift();
    test_martinez_ebar_period_shift();
    test_martinez_f_period_shift();
    test_martinez_g_period_shift();
    test_martinez_h_period_shift();
    return 0;
}
