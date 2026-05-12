#ifndef COOK_DATA_BLOCK_H
#define COOK_DATA_BLOCK_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_DATA_BLOCK_WIDTH_PER_BIT;

void cook_data_block_emit(uint8_t *out, size_t pos, size_t buf_len,
                          const uint8_t *tape_bits, size_t tape_len);

#endif
