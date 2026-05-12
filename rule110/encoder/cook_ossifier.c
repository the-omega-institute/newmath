#include "cook_ossifier.h"
#include <string.h>

const size_t COOK_OSSIFIER_WIDTH_PER_BIT = 30;

void cook_ossifier_emit(uint8_t *out, size_t pos, size_t buf_len,
                        const uint8_t *production_bits,
                        size_t production_len) {
    static const uint8_t ZERO_BIT_PATTERN[30] = {
        1, 0, 1, 0, 0, 1, 1, 1, 0, 0,
        1, 0, 1, 1, 0, 1, 0, 0, 1, 0,
        1, 1, 0, 1, 0, 0, 1, 0, 1, 1
    };
    static const uint8_t ONE_BIT_PATTERN[30] = {
        1, 1, 0, 1, 0, 1, 0, 0, 1, 1,
        1, 0, 1, 1, 0, 0, 1, 0, 1, 1,
        1, 0, 0, 1, 0, 1, 1, 1, 0, 1
    };
    const size_t width = COOK_OSSIFIER_WIDTH_PER_BIT;

    if (out == NULL) return;
    if (production_len == 0) return;
    if (production_bits == NULL) return;
    if (pos > buf_len) return;
    if (production_len > (buf_len - pos) / width) return;

    for (size_t i = 0; i < production_len; i++) {
        const uint8_t *pattern =
            production_bits[i] == 0 ? ZERO_BIT_PATTERN : ONE_BIT_PATTERN;
        memcpy(out + pos + (i * width), pattern, width);
    }
}
