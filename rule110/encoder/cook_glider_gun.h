#ifndef COOK_GLIDER_GUN_H
#define COOK_GLIDER_GUN_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_GLIDER_GUN_WIDTH;
extern const size_t COOK_GLIDER_GUN_EMISSION_PERIOD;

void cook_glider_gun_emit(uint8_t *out, size_t pos, size_t buf_len);
int cook_glider_gun_emit_phase_exact(uint8_t *out,
                                     size_t pos,
                                     size_t buf_len,
                                     const char *neighbor,
                                     int phase);

#endif
