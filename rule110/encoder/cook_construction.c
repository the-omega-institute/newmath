#include "cook_construction.h"
#include <string.h>

const uint8_t COOK_ETHER_PATTERN[COOK_ETHER_WIDTH] =
    {0, 0, 0, 1, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1};

void cook_ether_emit(uint8_t *out, size_t period_count) {
    for (size_t i = 0; i < period_count; i++) {
        memcpy(out + (i * COOK_ETHER_WIDTH),
               COOK_ETHER_PATTERN,
               COOK_ETHER_WIDTH);
    }
}

void cook_glider_A_emit(uint8_t *out, size_t pos, size_t ether_width) {
    static const uint8_t GLIDER_A_ROW0[4] = {1, 0, 1, 1};

    /*
       Cook's catalog gives glider A as a period-(3,2) particle in the
       ether. This emitter uses the row-0 NKS/Cook visual-catalog
       approximation "1011" as a local overwrite of a pre-filled ether
       background. Later catalog tasks can replace this with phase-exact
       multi-row placement data without changing the caller contract.
    */
    if (pos > ether_width || sizeof(GLIDER_A_ROW0) > ether_width - pos) return;

    memcpy(out + pos, GLIDER_A_ROW0, sizeof(GLIDER_A_ROW0));
}
