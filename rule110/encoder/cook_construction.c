#include "cook_construction.h"
#include <string.h>

const uint8_t COOK_ETHER_PATTERN[COOK_ETHER_WIDTH] =
    {0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1};

static const uint8_t COOK_GLIDER_A_PHASE_ORBIT[4][6] = {
    {1, 1, 1, 1, 1, 0},
    {1, 0, 0, 0, 1, 1},
    {1, 0, 0, 1, 1, 0},
    {1, 0, 1, 1, 1, 1}
};

void cook_ether_emit(uint8_t *out, size_t period_count) {
    for (size_t i = 0; i < period_count; i++) {
        memcpy(out + (i * COOK_ETHER_WIDTH),
               COOK_ETHER_PATTERN,
               COOK_ETHER_WIDTH);
    }
}

void cook_glider_A_emit(uint8_t *out, size_t pos, size_t ether_width) {
    /*
       A(f1_1) from the Martinez-McIntosh-Seck-Chapa Rule 110 phase
       language. Direct Rule 110 evolution verifies this row word as a
       period-3, displacement-2 A phase.
    */
    if (pos > ether_width ||
        sizeof(COOK_GLIDER_A_PHASE_ORBIT[0]) > ether_width - pos) {
        return;
    }

    memcpy(out + pos,
           COOK_GLIDER_A_PHASE_ORBIT[0],
           sizeof(COOK_GLIDER_A_PHASE_ORBIT[0]));
}
