#include "cook_ossifier.h"
#include "cook_construction.h"
#include "glider_phases.h"
#include <string.h>

const size_t COOK_OSSIFIER_WIDTH_PER_BIT = 30;

#define COOK_OSSIFIER_A4S_PER_GROUP 4
#define COOK_OSSIFIER_A4_UP_TILES 5

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

static int cook_ossifier_tile_width(int tiles, size_t *width_out) {
    if (width_out == NULL || tiles < 0) return 0;
    return cook_ossifier_mul_size((size_t)tiles,
                                  (size_t)COOK_ETHER_WIDTH,
                                  width_out);
}

static int cook_ossifier_a4_group_width(size_t *width_out) {
    size_t a4_len = 0;
    size_t gap_width = 0;
    size_t width = 0;

    if (width_out == NULL) return 0;
    if (glider_phase("A", NULL, 1, &a4_len) == NULL) return 0;
    if (!cook_ossifier_tile_width(COOK_OSSIFIER_A4_UP_TILES, &gap_width)) {
        return 0;
    }
    width = a4_len;
    for (size_t i = 1; i < COOK_OSSIFIER_A4S_PER_GROUP; i++) {
        if (!cook_ossifier_add_size(width, gap_width, &width)) return 0;
        if (!cook_ossifier_add_size(width, a4_len, &width)) return 0;
    }

    *width_out = width;
    return 1;
}

static int cook_ossifier_packet_width(int k_spacing, size_t *width_out) {
    size_t offset_width = 0;
    size_t group_width = 0;

    if (width_out == NULL || k_spacing < 0) return 0;
    if (!cook_ossifier_tile_width(k_spacing, &offset_width)) return 0;
    if (!cook_ossifier_a4_group_width(&group_width)) return 0;
    return cook_ossifier_add_size(offset_width, group_width, width_out);
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

static int cook_ossifier_emit_a4_group(uint8_t *out,
                                       size_t pos,
                                       size_t buf_len,
                                       size_t a4_len) {
    size_t gap_width = 0;

    if (!cook_ossifier_tile_width(COOK_OSSIFIER_A4_UP_TILES, &gap_width)) {
        return 0;
    }
    for (size_t i = 0; i < COOK_OSSIFIER_A4S_PER_GROUP; i++) {
        if (glider_phase_emit(out,
                              pos + (i * (a4_len + gap_width)),
                              buf_len,
                              "A",
                              NULL,
                              4,
                              NULL) != 0) {
            return 0;
        }
    }

    return 1;
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

int cook_ossifier_branch_k(enum ossifier_input_kind input_kind,
                           enum ossifier_action action,
                           int *k_out) {
    if (k_out == NULL) return 0;
    if (input_kind == OSSIFIER_AFTER_INVISIBLE_EBAR) {
        if (action == OSSIFY_PRODUCE_C2) {
            *k_out = 0;
            return 1;
        }
        if (action == OSSIFY_CROSS) {
            *k_out = 1;
            return 1;
        }
        return 0;
    }
    if (input_kind == OSSIFIER_AFTER_MOVING_DATA) {
        if (action == OSSIFY_PRODUCE_C2) {
            *k_out = 4;
            return 1;
        }
        if (action == OSSIFY_CROSS) {
            *k_out = 5;
            return 1;
        }
    }
    return 0;
}

int cook_ossifier_emit_phase_exact(uint8_t *out, size_t pos, size_t buf_len,
                                   const uint8_t *production_bits,
                                   size_t production_len) {
    return cook_ossifier_emit_phase_exact_branch(out,
                                                pos,
                                                buf_len,
                                                production_bits,
                                                production_len,
                                                OSSIFIER_AFTER_INVISIBLE_EBAR,
                                                OSSIFY_PRODUCE_C2);
}

int cook_ossifier_emit_phase_exact_branch(uint8_t *out,
                                          size_t pos,
                                          size_t buf_len,
                                          const uint8_t *production_bits,
                                          size_t production_len,
                                          enum ossifier_input_kind input_kind,
                                          enum ossifier_action action) {
    size_t packet_width = 0;
    size_t a4_len = 0;
    size_t offset_width = 0;
    int k_spacing = 0;
    size_t cursor = pos;

    if (production_len > 0 && production_bits == NULL) {
        return COOK_OSSIFIER_PHASE_EXACT_CATALOG_MISSING;
    }
    if (!cook_ossifier_branch_k(input_kind, action, &k_spacing)) {
        return COOK_OSSIFIER_PHASE_EXACT_CATALOG_MISSING;
    }
    if (glider_phase("A", NULL, 1, &a4_len) == NULL) {
        return COOK_OSSIFIER_PHASE_EXACT_CATALOG_MISSING;
    }
    if (!cook_ossifier_tile_width(k_spacing, &offset_width)) {
        return COOK_OSSIFIER_PHASE_EXACT_CATALOG_MISSING;
    }
    if (!cook_ossifier_packet_width(k_spacing, &packet_width)) {
        return COOK_OSSIFIER_PHASE_EXACT_CATALOG_MISSING;
    }
    if (!cook_ossifier_row_is_writable(out, pos, buf_len, packet_width)) {
        return COOK_OSSIFIER_PHASE_EXACT_CATALOG_MISSING;
    }

    cursor += offset_width;
    if (!cook_ossifier_emit_a4_group(out, cursor, buf_len, a4_len)) {
        return COOK_OSSIFIER_PHASE_EXACT_CATALOG_MISSING;
    }

    return COOK_OSSIFIER_PHASE_EXACT_OK;
}
