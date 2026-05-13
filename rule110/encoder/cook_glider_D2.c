#include "cook_glider_D2.h"
#include "glider_phases.h"

const size_t COOK_GLIDER_D2_WIDTH = 19;
const size_t COOK_GLIDER_D2_PERIOD = 10;
const int COOK_GLIDER_D2_VELOCITY = 2;

void cook_glider_D2_emit(uint8_t *out, size_t pos, size_t buf_len) {
    (void)cook_glider_D2_emit_phase_exact(out, pos, buf_len, "A", 1);
}

int cook_glider_D2_emit_phase_exact(uint8_t *out,
                                    size_t pos,
                                    size_t buf_len,
                                    const char *neighbor,
                                    int phase) {
    return glider_phase_emit(out, pos, buf_len, "D2", neighbor, phase, NULL);
}
