#include "cook_glider_B.h"
#include <string.h>

const size_t COOK_GLIDER_B_WIDTH = 3;
const size_t COOK_GLIDER_B_PERIOD = 4;
const int COOK_GLIDER_B_VELOCITY = -1;

void cook_glider_B_emit(uint8_t *out, size_t pos, size_t buf_len) {
    static const uint8_t GLIDER_B_ROW0[3] = {1, 0, 1};

    /*
       Best-effort row-0 perturbation for Cook/Martinez glider B.
       The chosen overwrite is the compact seed "101" on Cook ether
       phase 0. Direct Rule 110 evolution keeps the disturbance moving
       left while the far-field ether remains phase-aligned.
    */
    if (pos > buf_len || sizeof(GLIDER_B_ROW0) > buf_len - pos) return;

    memcpy(out + pos, GLIDER_B_ROW0, sizeof(GLIDER_B_ROW0));
}
