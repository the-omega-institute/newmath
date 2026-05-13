#include "cook_glider_E.h"
#include "glider_phases.h"
#include <string.h>

const size_t COOK_GLIDER_E_WIDTH = 6;
const size_t COOK_GLIDER_E_PERIOD = 7;
const int COOK_GLIDER_E_VELOCITY = -3;

void cook_glider_E_emit(uint8_t *out, size_t pos, size_t buf_len) {
    static const uint8_t GLIDER_E_ROW0[6] = {1, 1, 1, 0, 0, 1};

    /*
       Cook 2004, section 3, and the Martínez Rule 110 catalog identify E
       as one of the wider ether particles. This row is a visual-catalog
       phase approximation selected by direct Rule 110 motion testing on
       the Cook ether phase used by cook_ether_emit.
    */
    if (pos > buf_len || sizeof(GLIDER_E_ROW0) > buf_len - pos) return;

    memcpy(out + pos, GLIDER_E_ROW0, sizeof(GLIDER_E_ROW0));
}

int cook_glider_E_emit_phase_exact(uint8_t *out,
                                   size_t pos,
                                   size_t buf_len,
                                   const char *neighbor,
                                   int phase) {
    return glider_phase_emit(out, pos, buf_len, "Ebar", neighbor, phase, NULL);
}
