#include "cook_glider_H.h"
#include <string.h>

const size_t COOK_GLIDER_H_WIDTH = 14;
const size_t COOK_GLIDER_H_PERIOD = 14;
const int COOK_GLIDER_H_VELOCITY = -4;

void cook_glider_H_emit(uint8_t *out, size_t pos, size_t buf_len) {
    static const uint8_t GLIDER_H_ROW0[14] =
        {1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0};

    /*
       Cook 2004, section 3, and secondary Rule 110 catalogs include H in
       the eight-family glider list. This row is a phase approximation that
       gives a persistent moving perturbation over the encoded ether.
    */
    if (pos > buf_len || sizeof(GLIDER_H_ROW0) > buf_len - pos) return;

    memcpy(out + pos, GLIDER_H_ROW0, sizeof(GLIDER_H_ROW0));
}
