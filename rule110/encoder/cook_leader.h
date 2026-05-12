#ifndef COOK_LEADER_H
#define COOK_LEADER_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_LEADER_WIDTH;
extern const size_t COOK_LEADER_STABILITY_STEPS;

void cook_leader_emit(uint8_t *out, size_t pos, size_t buf_len);

#endif
