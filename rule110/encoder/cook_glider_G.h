#ifndef COOK_GLIDER_G_H
#define COOK_GLIDER_G_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_GLIDER_G_WIDTH;
extern const size_t COOK_GLIDER_G_PERIOD;
extern const int COOK_GLIDER_G_VELOCITY;

void cook_glider_G_emit(uint8_t *out, size_t pos, size_t buf_len);

#endif
