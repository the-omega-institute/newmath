#include "cook_leader.h"
#include "cook_construction.h"
#include "glider_phases.h"
#include <string.h>

const size_t COOK_LEADER_WIDTH = 20;
const size_t COOK_LEADER_STABILITY_STEPS = 500;

#define COOK_LEADER_EBAR_COUNT 8
#define COOK_LEADER_C2_COUNT 4
#define COOK_LEADER_INVISIBLE_COUNT 2
#define COOK_LEADER_MAX_A_COUNT 3
#define COOK_LEADER_ACCEPTOR_A_COUNT 3
#define COOK_LEADER_REJECTOR_A_COUNT 1
#define COOK_LEADER_A_SPACING_TILES 3
#define COOK_LEADER_SHORT_UP_TILES 3
#define COOK_LEADER_PREPARED_MODULUS 4

typedef struct {
    int ebar_spacing_tiles;
    int invisible_alignment_tiles;
    int ebar_to_c2_tiles;
    int c2_spacing_tiles;
    int c2_phases[COOK_LEADER_C2_COUNT];
    int a_phases[COOK_LEADER_MAX_A_COUNT];
    int a_count;
} CookLeaderLayout;

static const CookLeaderLayout COOK_LEADER_ACCEPT_LAYOUT = {
    3,
    5,
    3,
    3,
    {1, 2, 3, 4},
    {4, 1, 1},
    COOK_LEADER_ACCEPTOR_A_COUNT
};

static const CookLeaderLayout COOK_LEADER_REJECT_LAYOUT = {
    2,
    1,
    4,
    5,
    {4, 3, 2, 1},
    {3, 0, 0},
    COOK_LEADER_REJECTOR_A_COUNT
};

static int cook_leader_add_size(size_t left, size_t right, size_t *out) {
    if (left > ((size_t)-1) - right) return 0;
    *out = left + right;
    return 1;
}

static int cook_leader_mul_size(size_t left, size_t right, size_t *out) {
    if (left != 0 && right > ((size_t)-1) / left) return 0;
    *out = left * right;
    return 1;
}

int cook_leader_prepared_k(enum leader_prepared_context context,
                           size_t c,
                           int *k_out) {
    size_t raw = 0;

    if (k_out == NULL || c == 0 || c % 6u != 0) return 0;
    if (context == LEADER_PREPARED_AFTER_MOVING_DATA) {
        *k_out = 0;
        return 1;
    }
    if (context == LEADER_PREPARED_AFTER_REJECTED_INVISIBLES) {
        if (!cook_leader_mul_size(c, 10u, &raw)) return 0;
        if (!cook_leader_add_size(raw, 2u, &raw)) return 0;
        *k_out = (int)(raw % 6u);
        return 1;
    }
    return 0;
}

int cook_leader_prepared_invisible_alignment(
    enum leader_prepared_context context,
    size_t c,
    int *alignment_out) {
    int k = 0;

    if (alignment_out == NULL) return 0;
    if (!cook_leader_prepared_k(context, c, &k)) return 0;
    *alignment_out = (k + 5) % 6;
    return 1;
}

static int cook_leader_add_mod4(int left, int right) {
    int value = (left + right) % COOK_LEADER_PREPARED_MODULUS;

    return value < 0 ? value + COOK_LEADER_PREPARED_MODULUS : value;
}

int cook_leader_prepared_placement(size_t c,
                                   CookLeaderPreparedPlacement *placement_out) {
    CookLeaderPreparedPlacement placement;
    size_t y_repeats = 0;
    int total = 0;
    int y_pair = 0;

    if (placement_out == NULL || c == 0 || c % 6u != 0) return 0;
    if (c > ((size_t)-1) / 2u) return 0;
    y_repeats = (2u * c) - 1u;
    if (y_repeats > ((size_t)-1) / 3u) return 0;

    placement.v[0] = 0;
    placement.v[1] = 1;
    placement.w[0] = 2;
    placement.w[1] = 3;
    placement.x[0] = 1;
    placement.x[1] = 0;
    placement.y[0] = 1;
    placement.y[1] = 0;
    placement.y[2] = 3;
    placement.y[3] = 0;
    placement.y[4] = 3;
    placement.y[5] = 0;
    placement.y_repeats = y_repeats;

    total = cook_leader_add_mod4(total, placement.v[1]);
    total = cook_leader_add_mod4(total, placement.x[1]);
    total = cook_leader_add_mod4(total, placement.w[1]);
    y_pair = cook_leader_add_mod4(placement.y[1], placement.y[2]);
    total = cook_leader_add_mod4(
        total,
        (int)((y_repeats * (size_t)y_pair) %
              (size_t)COOK_LEADER_PREPARED_MODULUS));
    total = cook_leader_add_mod4(total, placement.y[5]);
    placement.total_mod4 = total;

    if (placement.total_mod4 != 1) return 0;
    *placement_out = placement;
    return 1;
}

static int cook_leader_layout_for_context(const CookLeaderLayout *base,
                                          enum leader_prepared_context context,
                                          size_t c,
                                          CookLeaderLayout *out) {
    int alignment = 0;
    CookLeaderPreparedPlacement placement;

    if (base == NULL || out == NULL) return 0;
    if (!cook_leader_prepared_invisible_alignment(context, c, &alignment)) {
        return 0;
    }
    if (!cook_leader_prepared_placement(c, &placement)) return 0;
    *out = *base;
    out->invisible_alignment_tiles = alignment;
    return 1;
}

static int cook_leader_ebar_spacing_for_pair(const CookLeaderLayout *layout,
                                             size_t left_index) {
    if (left_index == 0) return layout->invisible_alignment_tiles;
    return layout->ebar_spacing_tiles;
}

static int cook_leader_step_width(int spacing_tiles,
                                  size_t glider_len,
                                  size_t *width_out) {
    size_t gap_width = 0;

    if (spacing_tiles < 0 || width_out == NULL) return 0;
    if (!cook_leader_mul_size((size_t)spacing_tiles,
                              (size_t)COOK_ETHER_WIDTH,
                              &gap_width)) {
        return 0;
    }
    return cook_leader_add_size(glider_len, gap_width, width_out);
}

static int cook_leader_tile_width(int spacing_tiles, size_t *width_out) {
    if (spacing_tiles < 0 || width_out == NULL) return 0;
    return cook_leader_mul_size((size_t)spacing_tiles,
                                (size_t)COOK_ETHER_WIDTH,
                                width_out);
}

static int cook_leader_packet_width(const CookLeaderLayout *layout,
                                    enum leader_kind kind,
                                    size_t *width_out) {
    size_t ebar_len = 0;
    size_t c2_len = 0;
    size_t a_len = 0;
    size_t width = 0;
    size_t step = 0;

    if (layout == NULL || width_out == NULL) return 0;
    if (glider_phase("Ebar", "A", 1, &ebar_len) == NULL) return 0;
    if (glider_phase("C2", "A", 1, &c2_len) == NULL) return 0;
    if (glider_phase("A", NULL, 1, &a_len) == NULL) return 0;

    width = ebar_len;
    if (kind == LEADER_SHORT) {
        if (!cook_leader_tile_width(COOK_LEADER_SHORT_UP_TILES, &step)) {
            return 0;
        }
        if (!cook_leader_add_size(width, step, &width)) return 0;
    } else if (kind != LEADER_REGULAR) {
        return 0;
    }
    for (size_t i = 1; i < COOK_LEADER_INVISIBLE_COUNT; i++) {
        if (!cook_leader_step_width(cook_leader_ebar_spacing_for_pair(layout,
                                                                      i - 1),
                                    ebar_len,
                                    &step)) {
            return 0;
        }
        if (!cook_leader_add_size(width, step, &width)) return 0;
    }

    if (!cook_leader_step_width(cook_leader_ebar_spacing_for_pair(
                                    layout,
                                    COOK_LEADER_INVISIBLE_COUNT - 1),
                                ebar_len,
                                &step)) {
        return 0;
    }
    if (!cook_leader_add_size(width, step, &width)) return 0;

    for (size_t i = COOK_LEADER_INVISIBLE_COUNT + 1;
         i < COOK_LEADER_EBAR_COUNT;
         i++) {
        if (!cook_leader_step_width(cook_leader_ebar_spacing_for_pair(layout,
                                                                      i - 1),
                                    ebar_len,
                                    &step)) {
            return 0;
        }
        if (!cook_leader_add_size(width, step, &width)) return 0;
    }

    if (!cook_leader_step_width(layout->ebar_to_c2_tiles,
                                ebar_len,
                                &step)) {
        return 0;
    }
    if (!cook_leader_add_size(width, step, &width)) return 0;
    if (c2_len > ebar_len &&
        !cook_leader_add_size(width, c2_len - ebar_len, &width)) {
        return 0;
    }

    for (size_t i = 1; i < COOK_LEADER_C2_COUNT; i++) {
        if (!cook_leader_step_width(layout->c2_spacing_tiles,
                                    c2_len,
                                    &step)) {
            return 0;
        }
        if (!cook_leader_add_size(width, step, &width)) return 0;
    }

    if (layout->a_count > 0) {
        if (!cook_leader_step_width(layout->c2_spacing_tiles,
                                    c2_len,
                                    &step)) {
            return 0;
        }
        if (!cook_leader_add_size(width, step, &width)) return 0;
        if (a_len > c2_len &&
            !cook_leader_add_size(width, a_len - c2_len, &width)) {
            return 0;
        }
        for (int i = 1; i < layout->a_count; i++) {
            if (!cook_leader_step_width(COOK_LEADER_A_SPACING_TILES,
                                        a_len,
                                        &step)) {
                return 0;
            }
            if (!cook_leader_add_size(width, step, &width)) return 0;
        }
    }

    *width_out = width;
    return 1;
}

static int cook_leader_row_is_writable(const uint8_t *out,
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

void cook_leader_emit(uint8_t *out, size_t pos, size_t buf_len) {
    static const uint8_t LEADER_ROW0[20] =
        {1, 0, 1, 1, 1, 1, 1, 1, 0, 1,
         0, 1, 0, 0, 0, 0, 1, 1, 0, 0};

    /*
       Best-effort Cook leader seed for the phase-B behavioral encoder.
       The row-0 overwrite is "10111111010100001100" on a pre-filled
       Cook ether background. It was selected by direct local Rule 110
       simulation because it leaves a detectable localized disturbance
       after 500 steps while preserving far-field ether in the tested
       light-cone guards. This is not a phase-exact transcription of
       Cook 2004 section 5.
    */
    if (pos > buf_len || COOK_LEADER_WIDTH > buf_len - pos) return;

    memcpy(out + pos, LEADER_ROW0, sizeof(LEADER_ROW0));
}

static int cook_leader_emit_layout(uint8_t *out,
                                   size_t pos,
                                   size_t buf_len,
                                   const CookLeaderLayout *layout,
                                   enum leader_kind kind) {
    size_t width = 0;
    size_t ebar_len = 0;
    size_t c2_len = 0;
    size_t a_len = 0;
    size_t cursor = pos;
    static const int ebar_phases[COOK_LEADER_EBAR_COUNT] =
        {1, 2, 3, 4, 1, 2, 3, 4};

    if (!cook_leader_packet_width(layout, kind, &width)) {
        return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
    }
    if (!cook_leader_row_is_writable(out, pos, buf_len, width)) {
        return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
    }
    if (glider_phase("Ebar", "A", 1, &ebar_len) == NULL ||
        glider_phase("C2", "A", 1, &c2_len) == NULL ||
        glider_phase("A", NULL, 1, &a_len) == NULL) {
        return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
    }
    if (kind == LEADER_SHORT) {
        size_t step = 0;

        if (!cook_leader_tile_width(COOK_LEADER_SHORT_UP_TILES, &step)) {
            return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
        }
        cursor += step;
    } else if (kind != LEADER_REGULAR) {
        return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
    }

    for (size_t i = 0; i < COOK_LEADER_EBAR_COUNT; i++) {
        size_t step = 0;
        int phase = ebar_phases[i];

        if (layout == &COOK_LEADER_REJECT_LAYOUT &&
            i >= COOK_LEADER_INVISIBLE_COUNT) {
            phase = ebar_phases[COOK_LEADER_EBAR_COUNT - 1 - i];
        }

        if (glider_phase_emit(out,
                              cursor,
                              buf_len,
                              "Ebar",
                              "A",
                              phase,
                              NULL) != 0) {
            return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
        }
        if (i + 1 < COOK_LEADER_EBAR_COUNT) {
            if (!cook_leader_step_width(cook_leader_ebar_spacing_for_pair(
                                            layout,
                                            i),
                                        ebar_len,
                                        &step)) {
                return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
            }
            cursor += step;
        }
    }

    {
        size_t step = 0;

        if (!cook_leader_step_width(layout->ebar_to_c2_tiles,
                                    ebar_len,
                                    &step)) {
            return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
        }
        cursor += step;
    }

    for (size_t i = 0; i < COOK_LEADER_C2_COUNT; i++) {
        size_t step = 0;

        if (glider_phase_emit(out,
                              cursor,
                              buf_len,
                              "C2",
                              "A",
                              layout->c2_phases[i],
                              NULL) != 0) {
            return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
        }
        if (i + 1 < COOK_LEADER_C2_COUNT) {
            if (!cook_leader_step_width(layout->c2_spacing_tiles,
                                        c2_len,
                                        &step)) {
                return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
            }
            cursor += step;
        }
    }

    if (layout->a_count > 0) {
        size_t step = 0;

        if (!cook_leader_step_width(layout->c2_spacing_tiles,
                                    c2_len,
                                    &step)) {
            return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
        }
        cursor += step;

        for (int i = 0; i < layout->a_count; i++) {
            if (glider_phase_emit(out,
                                  cursor,
                                  buf_len,
                                  "A",
                                  NULL,
                                  layout->a_phases[i],
                                  NULL) != 0) {
                return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
            }
            if (i + 1 < layout->a_count) {
                if (!cook_leader_step_width(COOK_LEADER_A_SPACING_TILES,
                                            a_len,
                                            &step)) {
                    return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
                }
                cursor += step;
            }
        }
    }

    return COOK_LEADER_PHASE_EXACT_OK;
}

int cook_leader_emit_phase_exact_accept(uint8_t *out,
                                        size_t pos,
                                        size_t buf_len) {
    return cook_leader_emit_phase_exact_accept_kind(out,
                                                    pos,
                                                    buf_len,
                                                    LEADER_REGULAR);
}

int cook_leader_emit_phase_exact_accept_kind(uint8_t *out,
                                             size_t pos,
                                             size_t buf_len,
                                             enum leader_kind kind) {
    return cook_leader_emit_phase_exact_accept_prepared(
        out,
        pos,
        buf_len,
        kind,
        LEADER_PREPARED_AFTER_MOVING_DATA,
        6u);
}

int cook_leader_emit_phase_exact_accept_prepared(
    uint8_t *out,
    size_t pos,
    size_t buf_len,
    enum leader_kind kind,
    enum leader_prepared_context context,
    size_t c) {
    CookLeaderLayout layout;

    if (!cook_leader_layout_for_context(&COOK_LEADER_ACCEPT_LAYOUT,
                                        context,
                                        c,
                                        &layout)) {
        return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
    }
    return cook_leader_emit_layout(out,
                                   pos,
                                   buf_len,
                                   &layout,
                                   kind);
}

int cook_leader_emit_phase_exact_reject(uint8_t *out,
                                        size_t pos,
                                        size_t buf_len) {
    return cook_leader_emit_phase_exact_reject_kind(out,
                                                    pos,
                                                    buf_len,
                                                    LEADER_REGULAR);
}

int cook_leader_emit_phase_exact_reject_kind(uint8_t *out,
                                             size_t pos,
                                             size_t buf_len,
                                             enum leader_kind kind) {
    return cook_leader_emit_phase_exact_reject_prepared(
        out,
        pos,
        buf_len,
        kind,
        LEADER_PREPARED_AFTER_REJECTED_INVISIBLES,
        6u);
}

int cook_leader_emit_phase_exact_reject_prepared(
    uint8_t *out,
    size_t pos,
    size_t buf_len,
    enum leader_kind kind,
    enum leader_prepared_context context,
    size_t c) {
    CookLeaderLayout layout;

    if (!cook_leader_layout_for_context(&COOK_LEADER_REJECT_LAYOUT,
                                        context,
                                        c,
                                        &layout)) {
        return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
    }
    return cook_leader_emit_layout(out,
                                   pos,
                                   buf_len,
                                   &layout,
                                   kind);
}

int cook_leader_emit_phase_exact(uint8_t *out, size_t pos, size_t buf_len) {
    return cook_leader_emit_phase_exact_kind(out,
                                            pos,
                                            buf_len,
                                            LEADER_REGULAR);
}

int cook_leader_emit_phase_exact_kind(uint8_t *out,
                                      size_t pos,
                                      size_t buf_len,
                                      enum leader_kind kind) {
    return cook_leader_emit_phase_exact_accept_kind(out, pos, buf_len, kind);
}

int cook_leader_emit_phase_exact_kind_prepared(
    uint8_t *out,
    size_t pos,
    size_t buf_len,
    enum leader_kind kind,
    enum leader_prepared_context context,
    size_t c) {
    return cook_leader_emit_phase_exact_accept_prepared(out,
                                                        pos,
                                                        buf_len,
                                                        kind,
                                                        context,
                                                        c);
}
