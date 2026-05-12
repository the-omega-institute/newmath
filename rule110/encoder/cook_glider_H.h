#ifndef COOK_GLIDER_H_H
#define COOK_GLIDER_H_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_GLIDER_H_WIDTH;
extern const size_t COOK_GLIDER_H_PERIOD;
extern const int COOK_GLIDER_H_VELOCITY;

void cook_glider_H_emit(uint8_t *out, size_t pos, size_t buf_len);

#endif
