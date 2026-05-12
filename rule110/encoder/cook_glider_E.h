#ifndef COOK_GLIDER_E_H
#define COOK_GLIDER_E_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_GLIDER_E_WIDTH;
extern const size_t COOK_GLIDER_E_PERIOD;
extern const int COOK_GLIDER_E_VELOCITY;

void cook_glider_E_emit(uint8_t *out, size_t pos, size_t buf_len);

#endif
