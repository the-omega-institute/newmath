#include "cook_glider_D.h"
#include <string.h>

const size_t COOK_GLIDER_D_WIDTH = 5;
const size_t COOK_GLIDER_D_PERIOD = 4;
const int COOK_GLIDER_D_VELOCITY = -1;

void cook_glider_D_emit(uint8_t *out, size_t pos, size_t buf_len) {
    static const uint8_t GLIDER_D_ROW0[5] = {1, 1, 0, 1, 0};

    /*
       Best-effort row-0 perturbation for Cook/Martinez glider D.
       The chosen overwrite is the seed "11010" on Cook ether phase 0.
       In direct simulation it contracts to a compact left-moving defect
       relative to the ether phase.
    */
    if (pos > buf_len || sizeof(GLIDER_D_ROW0) > buf_len - pos) return;

    memcpy(out + pos, GLIDER_D_ROW0, sizeof(GLIDER_D_ROW0));
}
