#include "cook_glider_F.h"
#include <string.h>

const size_t COOK_GLIDER_F_WIDTH = 7;
const size_t COOK_GLIDER_F_PERIOD = 7;
const int COOK_GLIDER_F_VELOCITY = -2;

void cook_glider_F_emit(uint8_t *out, size_t pos, size_t buf_len) {
    static const uint8_t GLIDER_F_ROW0[7] = {1, 1, 0, 0, 1, 0, 1};

    /*
       Cook 2004, section 3, and the Martínez Rule 110 catalog list F as a
       distinct ether particle family. This emitter records a single-row
       phase approximation whose localized perturbation remains mobile in
       the project evaluator.
    */
    if (pos > buf_len || sizeof(GLIDER_F_ROW0) > buf_len - pos) return;

    memcpy(out + pos, GLIDER_F_ROW0, sizeof(GLIDER_F_ROW0));
}
