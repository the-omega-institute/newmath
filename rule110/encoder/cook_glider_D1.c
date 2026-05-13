#include "cook_glider_D1.h"
#include "glider_phases.h"

const size_t COOK_GLIDER_D1_WIDTH = 11;
const size_t COOK_GLIDER_D1_PERIOD = 10;
const int COOK_GLIDER_D1_VELOCITY = 2;

void cook_glider_D1_emit(uint8_t *out, size_t pos, size_t buf_len) {
    (void)cook_glider_D1_emit_phase_exact(out, pos, buf_len, "A", 1);
}

int cook_glider_D1_emit_phase_exact(uint8_t *out,
                                    size_t pos,
                                    size_t buf_len,
                                    const char *neighbor,
                                    int phase) {
    return glider_phase_emit(out, pos, buf_len, "D1", neighbor, phase, NULL);
}
