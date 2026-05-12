#include "cook_ossifier.h"
#include "cook_construction.h"
#include <string.h>

const size_t COOK_OSSIFIER_WIDTH_PER_BIT = 30;

#define COOK_OSSIFIER_A4_WIDTH 10
#define COOK_OSSIFIER_A4S_PER_GROUP 4
#define COOK_OSSIFIER_GROUP_COUNT 2
#define COOK_OSSIFIER_DEFAULT_K_SPACING 0

static const uint8_t COOK_OSSIFIER_PACKED_A4[COOK_OSSIFIER_A4_WIDTH] =
    {0, 0, 0, 1, 1, 1, 0, 1, 1, 1};

static int cook_ossifier_add_size(size_t left, size_t right, size_t *out) {
    if (left > ((size_t)-1) - right) return 0;
    *out = left + right;
    return 1;
}

static int cook_ossifier_mul_size(size_t left, size_t right, size_t *out) {
    if (left != 0 && right > ((size_t)-1) / left) return 0;
    *out = left * right;
    return 1;
}

static int cook_ossifier_packet_width(int k_spacing, size_t *width_out) {
    size_t group_width = 0;
    size_t gap_tiles = 0;
    size_t gap_width = 0;
    size_t packet_width = 0;

    if (width_out == NULL || k_spacing < 0) return 0;
    if (!cook_ossifier_mul_size(COOK_OSSIFIER_A4S_PER_GROUP,
                                COOK_OSSIFIER_A4_WIDTH,
                                &group_width)) {
        return 0;
    }
    if (!cook_ossifier_mul_size((size_t)k_spacing, 6, &gap_tiles)) return 0;
    if (!cook_ossifier_add_size(gap_tiles, 5, &gap_tiles)) return 0;
    if (!cook_ossifier_mul_size(gap_tiles,
                                (size_t)COOK_ETHER_WIDTH,
                                &gap_width)) {
        return 0;
    }
    if (!cook_ossifier_add_size(group_width, gap_width, &packet_width)) {
        return 0;
    }
    if (!cook_ossifier_add_size(packet_width, group_width, &packet_width)) {
        return 0;
    }

    *width_out = packet_width;
    return 1;
}

static int cook_ossifier_row_is_writable(const uint8_t *out,
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

static void cook_ossifier_emit_a4_group(uint8_t *out, size_t pos) {
    for (size_t i = 0; i < COOK_OSSIFIER_A4S_PER_GROUP; i++) {
        memcpy(out + pos + (i * COOK_OSSIFIER_A4_WIDTH),
               COOK_OSSIFIER_PACKED_A4,
               COOK_OSSIFIER_A4_WIDTH);
    }
}

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

int cook_ossifier_emit_phase_exact(uint8_t *out, size_t pos, size_t buf_len,
                                   const uint8_t *production_bits,
                                   size_t production_len) {
    size_t packet_width = 0;
    size_t group_width = COOK_OSSIFIER_A4S_PER_GROUP *
        (size_t)COOK_OSSIFIER_A4_WIDTH;
    size_t gap_width = 0;
    int k_spacing = COOK_OSSIFIER_DEFAULT_K_SPACING;

    if (production_len > 0 && production_bits != NULL) {
        k_spacing = production_bits[0] == 0 ? 0 : 1;
    }
    if (!cook_ossifier_packet_width(k_spacing, &packet_width)) {
        return COOK_OSSIFIER_PHASE_EXACT_CATALOG_MISSING;
    }
    if (!cook_ossifier_row_is_writable(out, pos, buf_len, packet_width)) {
        return COOK_OSSIFIER_PHASE_EXACT_CATALOG_MISSING;
    }

    gap_width = packet_width - (2 * group_width);
    cook_ossifier_emit_a4_group(out, pos);
    cook_ossifier_emit_a4_group(out, pos + group_width + gap_width);
    return COOK_OSSIFIER_PHASE_EXACT_OK;
}
