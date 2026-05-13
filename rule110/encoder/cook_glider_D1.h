#ifndef COOK_GLIDER_D1_H
#define COOK_GLIDER_D1_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_GLIDER_D1_WIDTH;
extern const size_t COOK_GLIDER_D1_PERIOD;
extern const int COOK_GLIDER_D1_VELOCITY;

void cook_glider_D1_emit(uint8_t *out, size_t pos, size_t buf_len);
int cook_glider_D1_emit_phase_exact(uint8_t *out,
                                    size_t pos,
                                    size_t buf_len,
                                    const char *neighbor,
                                    int phase);

#endif
