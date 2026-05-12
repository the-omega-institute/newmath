#ifndef COOK_GLIDER_B_H
#define COOK_GLIDER_B_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_GLIDER_B_WIDTH;
extern const size_t COOK_GLIDER_B_PERIOD;
extern const int COOK_GLIDER_B_VELOCITY;

void cook_glider_B_emit(uint8_t *out, size_t pos, size_t buf_len);

#endif
