#ifndef COOK_GLIDER_GUN_H
#define COOK_GLIDER_GUN_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_GLIDER_GUN_WIDTH;
extern const size_t COOK_GLIDER_GUN_EMISSION_PERIOD;

void cook_glider_gun_emit(uint8_t *out, size_t pos, size_t buf_len);

#endif
