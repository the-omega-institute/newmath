#ifndef COOK_OSSIFIER_H
#define COOK_OSSIFIER_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_OSSIFIER_WIDTH_PER_BIT;

#define COOK_OSSIFIER_PHASE_EXACT_OK 0
#define COOK_OSSIFIER_PHASE_EXACT_CATALOG_MISSING 1

enum ossifier_input_kind {
    OSSIFIER_AFTER_INVISIBLE_EBAR = 0,
    OSSIFIER_AFTER_MOVING_DATA = 1
};

enum ossifier_action {
    OSSIFY_PRODUCE_C2 = 0,
    OSSIFY_CROSS = 1
};

void cook_ossifier_emit(uint8_t *out, size_t pos, size_t buf_len,
                        const uint8_t *production_bits,
                        size_t production_len);
int cook_ossifier_branch_k(enum ossifier_input_kind input_kind,
                           enum ossifier_action action,
                           int *k_out);
int cook_ossifier_emit_phase_exact(uint8_t *out, size_t pos, size_t buf_len,
                                   const uint8_t *production_bits,
                                   size_t production_len);
int cook_ossifier_emit_phase_exact_branch(uint8_t *out,
                                          size_t pos,
                                          size_t buf_len,
                                          const uint8_t *production_bits,
                                          size_t production_len,
                                          enum ossifier_input_kind input_kind,
                                          enum ossifier_action action);

#endif
