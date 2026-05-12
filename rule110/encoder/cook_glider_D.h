#ifndef COOK_GLIDER_D_H
#define COOK_GLIDER_D_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_GLIDER_D_WIDTH;
extern const size_t COOK_GLIDER_D_PERIOD;
extern const int COOK_GLIDER_D_VELOCITY;

void cook_glider_D_emit(uint8_t *out, size_t pos, size_t buf_len);

#endif
