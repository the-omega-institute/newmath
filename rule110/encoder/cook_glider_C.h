#ifndef COOK_GLIDER_C_H
#define COOK_GLIDER_C_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_GLIDER_C_WIDTH;
extern const size_t COOK_GLIDER_C_PERIOD;
extern const int COOK_GLIDER_C_VELOCITY;

void cook_glider_C_emit(uint8_t *out, size_t pos, size_t buf_len);

#endif
