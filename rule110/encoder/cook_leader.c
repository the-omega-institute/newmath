#include "cook_leader.h"
#include "cook_construction.h"
#include "glider_phases.h"
#include <string.h>

const size_t COOK_LEADER_WIDTH = 20;
const size_t COOK_LEADER_STABILITY_STEPS = 500;

#define COOK_LEADER_EBAR_COUNT 8
#define COOK_LEADER_C2_COUNT 4
#define COOK_LEADER_EBAR_SPACING_TILES 3
#define COOK_LEADER_EBAR_TO_C2_TILES 3
#define COOK_LEADER_C2_SPACING_TILES 3

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

static int cook_leader_packet_width(size_t *width_out) {
    size_t ebar_len = 0;
    size_t c2_len = 0;
    size_t width = 0;
    size_t step = 0;

    if (width_out == NULL) return 0;
    if (glider_phase("Ebar", "A", 1, &ebar_len) == NULL) return 0;
    if (glider_phase("C2", "A", 1, &c2_len) == NULL) return 0;

    width = ebar_len;
    for (size_t i = 1; i < COOK_LEADER_EBAR_COUNT; i++) {
        if (!cook_leader_step_width(COOK_LEADER_EBAR_SPACING_TILES,
                                    ebar_len,
                                    &step)) {
            return 0;
        }
        if (!cook_leader_add_size(width, step, &width)) return 0;
    }

    if (!cook_leader_step_width(COOK_LEADER_EBAR_TO_C2_TILES,
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
        if (!cook_leader_step_width(COOK_LEADER_C2_SPACING_TILES,
                                    c2_len,
                                    &step)) {
            return 0;
        }
        if (!cook_leader_add_size(width, step, &width)) return 0;
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

int cook_leader_emit_phase_exact(uint8_t *out, size_t pos, size_t buf_len) {
    size_t width = 0;
    size_t ebar_len = 0;
    size_t c2_len = 0;
    size_t cursor = pos;
    static const int ebar_phases[COOK_LEADER_EBAR_COUNT] =
        {1, 2, 3, 4, 1, 2, 3, 4};
    static const int c2_phases[COOK_LEADER_C2_COUNT] =
        {1, 2, 3, 4};

    if (!cook_leader_packet_width(&width)) {
        return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
    }
    if (!cook_leader_row_is_writable(out, pos, buf_len, width)) {
        return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
    }
    if (glider_phase("Ebar", "A", 1, &ebar_len) == NULL ||
        glider_phase("C2", "A", 1, &c2_len) == NULL) {
        return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
    }

    for (size_t i = 0; i < COOK_LEADER_EBAR_COUNT; i++) {
        size_t step = 0;

        if (glider_phase_emit(out,
                              cursor,
                              buf_len,
                              "Ebar",
                              "A",
                              ebar_phases[i],
                              NULL) != 0) {
            return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
        }
        if (i + 1 < COOK_LEADER_EBAR_COUNT) {
            if (!cook_leader_step_width(COOK_LEADER_EBAR_SPACING_TILES,
                                        ebar_len,
                                        &step)) {
                return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
            }
            cursor += step;
        }
    }

    {
        size_t step = 0;

        if (!cook_leader_step_width(COOK_LEADER_EBAR_TO_C2_TILES,
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
                              c2_phases[i],
                              NULL) != 0) {
            return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
        }
        if (i + 1 < COOK_LEADER_C2_COUNT) {
            if (!cook_leader_step_width(COOK_LEADER_C2_SPACING_TILES,
                                        c2_len,
                                        &step)) {
                return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
            }
            cursor += step;
        }
    }

    return COOK_LEADER_PHASE_EXACT_OK;
}
