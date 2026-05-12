#ifndef COOK_CONSTRUCTION_H
#define COOK_CONSTRUCTION_H

#include <stddef.h>
#include <stdint.h>

#define COOK_ETHER_WIDTH 14
#define COOK_ETHER_PERIOD 7

extern const uint8_t COOK_ETHER_PATTERN[COOK_ETHER_WIDTH];

void cook_ether_emit(uint8_t *out, size_t period_count);
void cook_glider_A_emit(uint8_t *out, size_t pos, size_t ether_width);

#endif
