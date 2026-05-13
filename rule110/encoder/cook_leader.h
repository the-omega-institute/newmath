#ifndef COOK_LEADER_H
#define COOK_LEADER_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_LEADER_WIDTH;
extern const size_t COOK_LEADER_STABILITY_STEPS;

#define COOK_LEADER_PHASE_EXACT_OK 0
#define COOK_LEADER_PHASE_EXACT_CATALOG_MISSING 1

void cook_leader_emit(uint8_t *out, size_t pos, size_t buf_len);
int cook_leader_emit_phase_exact(uint8_t *out, size_t pos, size_t buf_len);
int cook_leader_emit_phase_exact_accept(uint8_t *out,
                                        size_t pos,
                                        size_t buf_len);
int cook_leader_emit_phase_exact_reject(uint8_t *out,
                                        size_t pos,
                                        size_t buf_len);

#endif
