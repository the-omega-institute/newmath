#ifndef COOK_GLIDER_F_H
#define COOK_GLIDER_F_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_GLIDER_F_WIDTH;
extern const size_t COOK_GLIDER_F_PERIOD;
extern const int COOK_GLIDER_F_VELOCITY;

void cook_glider_F_emit(uint8_t *out, size_t pos, size_t buf_len);

#endif
