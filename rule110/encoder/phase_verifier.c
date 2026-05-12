#include "phase_verifier.h"

#include "glider_phases.h"
#include "rule110.h"

#include <stdlib.h>
#include <string.h>

typedef struct {
    const char *name;
    int period_t;
    int shift_x;
} PhaseMetadata;

static const PhaseMetadata PHASE_METADATA[] = {
    {"A", 3, 2},
    {"B", 4, -2},
    {"C1", 7, 0},
    {"C2", 7, 0},
    {"C3", 7, 0},
    {"D1", 10, 2},
    {"D2", 10, 2},
    {"Ebar", 30, -8},
    {"E-", 30, -8},
    {"F", 36, -4},
    {"G", 42, -14},
    {"H", 92, -18}
};

static int same_name(const char *left, const char *right) {
    if (left == NULL || right == NULL) return left == right;
    if (strcmp(left, right) == 0) return 1;
    if (strcmp(left, "E-") == 0 && strcmp(right, "Ebar") == 0) return 1;
    if (strcmp(left, "Ebar") == 0 && strcmp(right, "E-") == 0) return 1;
    return 0;
}

static const PhaseMetadata *metadata_for(const char *glider_name) {
    for (size_t i = 0;
         i < sizeof(PHASE_METADATA) / sizeof(PHASE_METADATA[0]);
         i++) {
        if (same_name(glider_name, PHASE_METADATA[i].name)) {
            return &PHASE_METADATA[i];
        }
    }

    return NULL;
}

int phase_verifier_check(const char *glider_name,
                         const char *neighbor,
                         int phase) {
    size_t len = 0;
    const char *bits = glider_phase(glider_name, neighbor, phase, &len);
    const PhaseMetadata *metadata = metadata_for(glider_name);
    uint8_t *before = NULL;
    uint8_t *after = NULL;
    size_t guard = 0;
    size_t repeat_count = 0;
    size_t center = 0;
    size_t tape_len = 0;
    int result = PHV_NOT_PHASE_EXACT;

    if (bits == NULL) return PHV_NOT_REGISTERED;
    if (metadata == NULL) return PHV_NO_METADATA;
    if (len == 0) return PHV_NOT_PHASE_EXACT;

    guard = (size_t)metadata->period_t +
        (size_t)(metadata->shift_x < 0 ? -metadata->shift_x : metadata->shift_x) +
        2u;
    repeat_count = 2u * ((guard / len) + 2u) + 1u;
    center = (repeat_count / 2u) * len;
    tape_len = repeat_count * len;

    before = (uint8_t *)malloc(tape_len);
    after = (uint8_t *)malloc(tape_len);
    if (before == NULL || after == NULL) abort();

    for (size_t repeat = 0; repeat < repeat_count; repeat++) {
        for (size_t i = 0; i < len; i++) {
            if (bits[i] != '0' && bits[i] != '1') {
                free(before);
                free(after);
                return PHV_NOT_PHASE_EXACT;
            }
            before[repeat * len + i] = (uint8_t)(bits[i] == '1');
        }
    }
    memcpy(after, before, tape_len);

    r110_run_n_steps(after, tape_len, (size_t)metadata->period_t);
    result = PHV_OK;
    for (size_t i = 0; i < len; i++) {
        long src = (long)(center + i) - (long)metadata->shift_x;

        if (src < 0 || src >= (long)tape_len ||
            after[center + i] != before[(size_t)src]) {
            result = PHV_NOT_PHASE_EXACT;
            break;
        }
    }

    free(before);
    free(after);
    return result;
}
