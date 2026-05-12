#include "cook_data_block.h"
#include <string.h>

const size_t COOK_DATA_BLOCK_WIDTH_PER_BIT = 50;

static void cook_data_symbol_emit(uint8_t *out, size_t pos, uint8_t bit) {
    static const uint8_t SYMBOL_ZERO[18] =
        {1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0};
    static const uint8_t SYMBOL_ONE[28] =
        {1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1,
         0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1};

    /*
       Best-effort Cook data-block row templates. Each logical tape symbol
       receives a 50-cell ether-aligned slot so neighboring symbols stay
       distinguishable. The concrete rows are sparse local perturbations:
       logical 0 is a smaller pass-through marker; logical 1 is a wider
       production-trigger marker. These are behavioral placeholders pending
       phase-exact Cook 2004 section 6 diagrams.
    */
    if (bit == 0) {
        memcpy(out + pos, SYMBOL_ZERO, sizeof(SYMBOL_ZERO));
    } else {
        memcpy(out + pos, SYMBOL_ONE, sizeof(SYMBOL_ONE));
    }
}

void cook_data_block_emit(uint8_t *out, size_t pos, size_t buf_len,
                          const uint8_t *tape_bits, size_t tape_len) {
    size_t width;

    if (out == NULL || tape_len == 0) return;
    if (tape_bits == NULL) return;
    if (tape_len > ((size_t)-1) / COOK_DATA_BLOCK_WIDTH_PER_BIT) return;

    width = tape_len * COOK_DATA_BLOCK_WIDTH_PER_BIT;
    if (pos > buf_len || width > buf_len - pos) return;

    for (size_t i = 0; i < tape_len; i++) {
        uint8_t bit = tape_bits[i] == 0 ? 0 : 1;
        cook_data_symbol_emit(out,
                              pos + (i * COOK_DATA_BLOCK_WIDTH_PER_BIT),
                              bit);
    }
}
