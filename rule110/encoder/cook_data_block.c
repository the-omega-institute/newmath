#include "cook_data_block.h"
#include "cook_construction.h"
#include "glider_phases.h"
#include <string.h>

const size_t COOK_DATA_BLOCK_WIDTH_PER_BIT = 50;

#define COOK_DATA_BLOCK_C2_COUNT 4
#define COOK_DATA_BLOCK_PHASE_SYMBOL_STRIDE 867

static int cook_data_block_add_size(size_t left, size_t right, size_t *out) {
    if (left > ((size_t)-1) - right) return 0;
    *out = left + right;
    return 1;
}

static int cook_data_block_mul_size(size_t left, size_t right, size_t *out) {
    if (left != 0 && right > ((size_t)-1) / left) return 0;
    *out = left * right;
    return 1;
}

static int cook_data_block_spacing_width(int spacing_tiles,
                                         size_t glider_len,
                                         size_t *width_out) {
    size_t gap_width = 0;

    if (spacing_tiles < 0 || width_out == NULL) return 0;
    if (!cook_data_block_mul_size((size_t)spacing_tiles,
                                  (size_t)COOK_ETHER_WIDTH,
                                  &gap_width)) {
        return 0;
    }
    return cook_data_block_add_size(glider_len, gap_width, width_out);
}

static int cook_data_block_packet_width(const int spacings[3],
                                        size_t c2_len,
                                        size_t *width_out) {
    size_t width = c2_len;

    if (spacings == NULL || width_out == NULL) return 0;
    for (size_t i = 0; i < 3; i++) {
        size_t step = 0;

        if (!cook_data_block_spacing_width(spacings[i], c2_len, &step)) {
            return 0;
        }
        if (!cook_data_block_add_size(width, step, &width)) return 0;
    }

    *width_out = width;
    return 1;
}

static int cook_data_block_tape_width(const uint8_t *tape_bits,
                                      size_t tape_len,
                                      size_t c2_len,
                                      size_t *width_out) {
    size_t width = 0;

    if (tape_bits == NULL || width_out == NULL || tape_len == 0) return 0;

    for (size_t i = 0; i < tape_len; i++) {
        static const int Y_SPACINGS[3] = {18, 18, 14};
        static const int N_SPACINGS[3] = {28, 10, 14};
        const int *spacings = tape_bits[i] == 0 ? N_SPACINGS : Y_SPACINGS;
        size_t symbol_width = 0;

        if (!cook_data_block_packet_width(spacings, c2_len, &symbol_width)) {
            return 0;
        }
        if (!cook_data_block_add_size(width, symbol_width, &width)) return 0;
        if (i + 1 < tape_len) {
            size_t symbol_stride = COOK_DATA_BLOCK_PHASE_SYMBOL_STRIDE;

            if (symbol_stride < symbol_width) return 0;
            if (!cook_data_block_add_size(width,
                                          symbol_stride - symbol_width,
                                          &width)) {
                return 0;
            }
        }
    }

    *width_out = width;
    return 1;
}

static int cook_data_block_row_is_writable(const uint8_t *out,
                                           size_t pos,
                                           size_t buf_len,
                                           size_t width) {
    if (out == NULL) return 0;
    if (pos > buf_len || width > buf_len - pos) return 0;
    for (size_t i = 0; i < width; i++) {
        if (out[pos + i] != 0 && out[pos + i] != 1) return 0;
    }
    return 1;
}

static void cook_data_symbol_emit(uint8_t *out, size_t pos, uint8_t bit) {
    static const uint8_t SYMBOL_ZERO[18] =
        {1, 0, 1, 0, 0, 0, 1, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0};
    static const uint8_t SYMBOL_ONE[28] =
        {1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1,
         0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 0, 1};

    /*
       Behavioral data-block row templates. Each logical tape symbol receives
       a 50-cell ether-aligned slot so neighboring symbols stay distinguishable.
       Logical 0 is a smaller pass-through marker; logical 1 is wider.
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

int cook_data_block_emit_phase_exact(uint8_t *out, size_t pos, size_t buf_len,
                                     const uint8_t *tape_bits,
                                     size_t tape_len) {
    static const int Y_SPACINGS[3] = {18, 18, 14};
    static const int N_SPACINGS[3] = {28, 10, 14};
    size_t c2_len = 0;
    size_t width = 0;
    const char *c2_bits = glider_phase("C2", "A", 1, &c2_len);

    if (tape_len == 0 || tape_bits == NULL || c2_bits == NULL) {
        return COOK_DATA_BLOCK_PHASE_EXACT_CATALOG_MISSING;
    }
    if (!cook_data_block_tape_width(tape_bits, tape_len, c2_len, &width)) {
        return COOK_DATA_BLOCK_PHASE_EXACT_CATALOG_MISSING;
    }
    if (!cook_data_block_row_is_writable(out, pos, buf_len, width)) {
        return COOK_DATA_BLOCK_PHASE_EXACT_CATALOG_MISSING;
    }

    for (size_t symbol = 0; symbol < tape_len; symbol++) {
        const int *spacings = tape_bits[symbol] == 0 ? N_SPACINGS : Y_SPACINGS;
        size_t cursor = pos + (symbol * COOK_DATA_BLOCK_PHASE_SYMBOL_STRIDE);

        for (size_t i = 0; i < COOK_DATA_BLOCK_C2_COUNT; i++) {
            if (glider_phase_emit(out,
                                  cursor,
                                  buf_len,
                                  "C2",
                                  "A",
                                  1,
                                  NULL) != 0) {
                return COOK_DATA_BLOCK_PHASE_EXACT_CATALOG_MISSING;
            }
            if (i + 1 < COOK_DATA_BLOCK_C2_COUNT) {
                size_t step = 0;

                if (!cook_data_block_spacing_width(spacings[i],
                                                   c2_len,
                                                   &step)) {
                    return COOK_DATA_BLOCK_PHASE_EXACT_CATALOG_MISSING;
                }
                cursor += step;
            }
        }
    }

    return COOK_DATA_BLOCK_PHASE_EXACT_OK;
}
