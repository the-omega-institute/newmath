#include "rule110.h"
#include "glider_phases.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

typedef struct {
    const char *name;
    const char *neighbor;
    int phase;
    int period;
    int displacement;
} GliderPeriod;

static const GliderPeriod EXPECTED[] = {
    {"ether", NULL, 1, 7, 0},
    {"A", NULL, 1, 3, 2},
    {"B", NULL, 1, 4, -2},
    {"Bbar", "A", 1, 12, -6},
    {"Bbar", "A", 2, 12, -6},
    {"Bbar", "A", 3, 12, -6},
    {"Bbar", "A", 4, 12, -6},
    {"Bbar", "B", 1, 12, -6},
    {"Bbar", "B", 2, 12, -6},
    {"Bbar", "B", 3, 12, -6},
    {"Bbar", "B", 4, 12, -6},
    {"Bbar", "C", 1, 12, -6},
    {"Bbar", "C", 2, 12, -6},
    {"Bbar", "C", 3, 12, -6},
    {"Bbar", "C", 4, 12, -6},
    {"Bhat", "A", 1, 12, -6},
    {"Bhat", "A", 2, 12, -6},
    {"Bhat", "A", 3, 12, -6},
    {"Bhat", "A", 4, 12, -6},
    {"Bhat", "B", 1, 12, -6},
    {"Bhat", "B", 2, 12, -6},
    {"Bhat", "B", 3, 12, -6},
    {"Bhat", "B", 4, 12, -6},
    {"Bhat", "C", 1, 12, -6},
    {"Bhat", "C", 2, 12, -6},
    {"Bhat", "C", 3, 12, -6},
    {"Bhat", "C", 4, 12, -6},
    {"C1", "A", 1, 7, 0},
    {"C2", "A", 1, 7, 0},
    {"E", "A", 1, 15, -4},
    {"E", "A", 2, 15, -4},
    {"E", "A", 3, 15, -4},
    {"E", "A", 4, 15, -4},
    {"E", "B", 1, 15, -4},
    {"E", "B", 2, 15, -4},
    {"E", "B", 3, 15, -4},
    {"E", "B", 4, 15, -4},
    {"E", "C", 1, 15, -4},
    {"E", "C", 2, 15, -4},
    {"E", "C", 3, 15, -4},
    {"E", "C", 4, 15, -4},
    {"E", "D", 1, 15, -4},
    {"E", "D", 2, 15, -4},
    {"E", "D", 3, 15, -4},
    {"E", "D", 4, 15, -4},
    {"Ebar", "A", 1, 30, -8},
    {"Ebar", "E", 1, 30, -8},
    {"Ebar", "E", 2, 30, -8},
    {"Ebar", "E", 3, 30, -8},
    {"Ebar", "E", 4, 30, -8},
    {"Ebar", "F", 1, 30, -8},
    {"Ebar", "F", 2, 30, -8},
    {"Ebar", "F", 3, 30, -8},
    {"Ebar", "F", 4, 30, -8},
    {"Ebar", "G", 1, 30, -8},
    {"Ebar", "G", 2, 30, -8},
    {"Ebar", "G", 3, 30, -8},
    {"Ebar", "G", 4, 30, -8},
    {"Ebar", "H", 1, 30, -8},
    {"Ebar", "H", 2, 30, -8},
    {"Ebar", "H", 3, 30, -8},
    {"Ebar", "H", 4, 30, -8},
    {"F", "A", 2, 36, -4},
    {"F", "B", 2, 36, -4},
    {"F", "B", 3, 36, -4},
    {"F", "C", 1, 36, -4},
    {"F", "C", 2, 36, -4},
    {"F", "C", 3, 36, -4},
    {"F", "D", 1, 36, -4},
    {"F", "D", 2, 36, -4},
    {"F", "D", 3, 36, -4},
    {"F", "E", 1, 36, -4},
    {"F", "E", 2, 36, -4},
    {"F", "E", 3, 36, -4},
    {"F", "F", 1, 36, -4},
    {"F", "F", 2, 36, -4},
    {"F", "F", 3, 36, -4},
    {"F", "F", 4, 36, -4},
    {"F", "G", 1, 36, -4},
    {"F", "G", 2, 36, -4},
    {"F", "G", 3, 36, -4},
    {"F", "H", 2, 36, -4},
    {"F", "H", 3, 36, -4},
    {"F", "A2", 2, 36, -4},
    {"F", "A2", 3, 36, -4},
    {"F", "B2", 3, 36, -4},
    {"G", "B", 3, 42, -14},
    {"G", "C", 2, 42, -14},
    {"G", "C", 3, 42, -14},
    {"G", "D", 2, 42, -14},
    {"G", "D", 3, 42, -14},
    {"G", "E", 2, 42, -14},
    {"G", "E", 3, 42, -14},
    {"G", "F", 2, 42, -14},
    {"G", "F", 3, 42, -14},
    {"G", "G", 2, 42, -14},
    {"G", "G", 3, 42, -14},
    {"G", "H", 2, 42, -14},
    {"G", "H", 3, 42, -14},
    {"G", "A2", 1, 42, -14},
    {"G", "A2", 2, 42, -14},
    {"G", "A2", 3, 42, -14},
    {"G", "B2", 1, 42, -14},
    {"G", "B2", 2, 42, -14},
    {"G", "B2", 3, 42, -14},
    {"G", "C2", 2, 42, -14},
    {"G", "C2", 3, 42, -14},
    {"G", "A", 3, 42, -14},
    {"H", "A", 1, 92, -18},
    {"H", "B", 1, 92, -18},
    {"H", "B", 2, 92, -18},
    {"H", "B", 3, 92, -18},
    {"H", "C", 1, 92, -18},
    {"H", "C", 2, 92, -18},
    {"H", "C", 3, 92, -18},
    {"H", "D", 2, 92, -18},
    {"H", "D", 3, 92, -18},
    {"H", "E", 2, 92, -18},
    {"H", "E", 3, 92, -18},
    {"H", "F", 3, 92, -18},
    {"H", "G", 3, 92, -18},
    {"H", "H", 3, 92, -18},
    {"H", "A2", 2, 92, -18},
    {"H", "A2", 3, 92, -18},
    {"H", "B2", 2, 92, -18},
    {"H", "B2", 3, 92, -18},
    {"H", "C2", 2, 92, -18},
    {"H", "C2", 3, 92, -18},
    {"H", "D2", 2, 92, -18},
    {"H", "D2", 3, 92, -18},
    {"H", "E2", 1, 92, -18},
    {"H", "E2", 2, 92, -18},
    {"H", "E2", 3, 92, -18},
    {"H", "F2", 1, 92, -18},
    {"H", "F2", 2, 92, -18},
    {"H", "F2", 3, 92, -18},
    {"H", "G2", 1, 92, -18},
    {"H", "G2", 2, 92, -18},
    {"H", "G2", 3, 92, -18},
    {"H", "H2", 1, 92, -18},
    {"H", "H2", 2, 92, -18},
    {"H", "H2", 3, 92, -18},
    {"H", "H2", 4, 92, -18},
    {"H", "A3", 1, 92, -18},
    {"H", "A3", 2, 92, -18},
    {"H", "A3", 3, 92, -18},
    {"H", "B3", 2, 92, -18},
    {"H", "B3", 3, 92, -18},
    {"H", "C3", 2, 92, -18},
    {"H", "C3", 3, 92, -18},
    {"H", "D3", 2, 92, -18},
    {"H", "D3", 3, 92, -18},
    {"H", "E3", 2, 92, -18},
    {"H", "E3", 3, 92, -18},
    {"H", "F3", 2, 92, -18},
    {"H", "F3", 3, 92, -18},
    {"H", "G3", 2, 92, -18},
    {"H", "G3", 3, 92, -18},
    {"H", "H3", 2, 92, -18},
    {"H", "H3", 3, 92, -18},
    {"H", "A4", 2, 92, -18},
    {"H", "A4", 3, 92, -18},
    {"Gun", "B2", 3, 77, -20},
    {"Gun", "G2", 3, 77, -20},
    {"Gun", "H2", 2, 77, -20},
    {"Gun", "H2", 3, 77, -20},
    {"Gun", "A3", 1, 77, -20},
    {"Gun", "A3", 2, 77, -20},
    {"Gun", "A3", 3, 77, -20},
    {"Gun", "B3", 1, 77, -20},
    {"Gun", "B3", 2, 77, -20},
    {"Gun", "B3", 3, 77, -20},
    {"Gun", "C3", 2, 77, -20},
    {"Gun", "C3", 3, 77, -20},
    {"Gun", "D3", 2, 77, -20},
    {"Gun", "D3", 3, 77, -20},
    {"Gun", "E3", 1, 77, -20}
};

static int verify_glider_period(const GliderPeriod *entry) {
    enum { REPEAT_COUNT = 41 };
    uint8_t *cells = NULL;
    uint8_t *before = NULL;
    size_t len = 0;
    const char *bits =
        glider_phase(entry->name, entry->neighbor, entry->phase, &len);
    size_t tape_len = 0;
    size_t center = 0;
    int result = 0;

    if (bits == NULL || len == 0) {
        printf("  %s(%s,f%d_1): FAIL missing registered phase\n",
               entry->name,
               entry->neighbor == NULL ? "-" : entry->neighbor,
               entry->phase);
        return 1;
    }

    tape_len = REPEAT_COUNT * len;
    center = (REPEAT_COUNT / 2u) * len;
    cells = (uint8_t *)malloc(tape_len);
    before = (uint8_t *)malloc(tape_len);
    if (cells == NULL || before == NULL) abort();

    for (size_t repeat = 0; repeat < REPEAT_COUNT; repeat++) {
        for (size_t i = 0; i < len; i++) {
            if (bits[i] != '0' && bits[i] != '1') abort();
            cells[repeat * len + i] = (uint8_t)(bits[i] == '1');
            before[repeat * len + i] = cells[repeat * len + i];
        }
    }

    r110_run_n_steps(cells, tape_len, (size_t)entry->period);
    for (size_t i = 0; i < len; i++) {
        long src = (long)(center + i) - (long)entry->displacement;

        if (src < 0 || src >= (long)tape_len ||
            cells[center + i] != before[(size_t)src]) {
            result = 1;
            break;
        }
    }

    free(cells);
    free(before);

    if (result) {
        printf("  %s(%s,f%d_1): FAIL period=%d displacement=%d\n",
               entry->name,
               entry->neighbor == NULL ? "-" : entry->neighbor,
               entry->phase,
               entry->period,
               entry->displacement);
        return 1;
    }

    printf("  %s(%s,f%d_1) period=%d displacement=%d: PASS\n",
           entry->name,
           entry->neighbor == NULL ? "-" : entry->neighbor,
           entry->phase,
           entry->period,
           entry->displacement);
    return 0;
}

int main(void) {
    int fail = 0;

    printf("== test_phase_verifier_martinez ==\n");
    for (size_t i = 0; i < sizeof(EXPECTED) / sizeof(EXPECTED[0]); i++) {
        fail += verify_glider_period(&EXPECTED[i]);
    }

    if (fail) {
        printf("FAIL %d period mismatch(es)\n", fail);
        return 1;
    }

    printf("ALL test_phase_verifier_martinez tests passed\n");
    return 0;
}
