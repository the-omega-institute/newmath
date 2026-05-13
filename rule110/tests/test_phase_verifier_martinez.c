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
    {"C1", "A", 1, 7, 0},
    {"C2", "A", 1, 7, 0},
    {"Ebar", "A", 1, 30, -8},
    {"F", "A", 2, 36, -4},
    {"G", "A", 3, 42, -14},
    {"H", "A", 1, 92, -18}
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
        printf("  %s: FAIL missing registered phase\n", entry->name);
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
        printf("  %s: FAIL period=%d displacement=%d\n",
               entry->name,
               entry->period,
               entry->displacement);
        return 1;
    }

    printf("  %s period=%d displacement=%d: PASS\n",
           entry->name,
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
