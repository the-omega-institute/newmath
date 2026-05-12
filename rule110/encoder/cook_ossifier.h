#ifndef COOK_OSSIFIER_H
#define COOK_OSSIFIER_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_OSSIFIER_WIDTH_PER_BIT;

void cook_ossifier_emit(uint8_t *out, size_t pos, size_t buf_len,
                        const uint8_t *production_bits,
                        size_t production_len);

#endif
