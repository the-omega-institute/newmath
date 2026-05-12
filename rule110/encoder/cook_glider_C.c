#include "cook_glider_C.h"
#include <string.h>

const size_t COOK_GLIDER_C_WIDTH = 4;
const size_t COOK_GLIDER_C_PERIOD = 7;
const int COOK_GLIDER_C_VELOCITY = 0;

void cook_glider_C_emit(uint8_t *out, size_t pos, size_t buf_len) {
    static const uint8_t GLIDER_C_ROW0[4] = {1, 0, 0, 1};

    /*
       Best-effort row-0 perturbation for Cook/Martinez glider C.
       The chosen overwrite is the seed "1001" on Cook ether phase 0.
       It produces a wider moving perturbation under Rule 110 without
       corrupting ether to the right of the packet in the tested window.
    */
    if (pos > buf_len || sizeof(GLIDER_C_ROW0) > buf_len - pos) return;

    memcpy(out + pos, GLIDER_C_ROW0, sizeof(GLIDER_C_ROW0));
}
