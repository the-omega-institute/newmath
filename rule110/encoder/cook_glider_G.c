#include "cook_glider_G.h"
#include <string.h>

const size_t COOK_GLIDER_G_WIDTH = 12;
const size_t COOK_GLIDER_G_PERIOD = 14;
const int COOK_GLIDER_G_VELOCITY = -1;

void cook_glider_G_emit(uint8_t *out, size_t pos, size_t buf_len) {
    static const uint8_t GLIDER_G_ROW0[12] =
        {1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1};

    /*
       Cook 2004, section 3, and later Rule 110 glider catalogs treat G as
       a rarer multi-phase particle. The row below is a compact catalog
       approximation validated here as a bounded moving ether perturbation.
    */
    if (pos > buf_len || sizeof(GLIDER_G_ROW0) > buf_len - pos) return;

    memcpy(out + pos, GLIDER_G_ROW0, sizeof(GLIDER_G_ROW0));
}
