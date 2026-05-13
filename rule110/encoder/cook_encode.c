#include "cook_encode.h"
#include "cook_construction.h"
#include "cook_data_block.h"
#include "cook_leader.h"
#include "cook_ossifier.h"

#define COOK_ENCODE_EMPTY_ETHER_PERIODS 50
#define COOK_ENCODE_EMPTY_LEADER_POS 100
#define COOK_ENCODE_TAPE_GUARD_PERIODS 12

static int add_size(size_t a, size_t b, size_t *out) {
    if (a > ((size_t)-1) - b) return -1;
    *out = a + b;
    return 0;
}

static int round_up_ether_width(size_t in, size_t *out) {
    size_t rem = in % (size_t)COOK_ETHER_WIDTH;

    if (rem == 0) {
        *out = in;
        return 0;
    }
    return add_size(in, (size_t)COOK_ETHER_WIDTH - rem, out);
}

#define COOK_ENCODE_ONE_ETHER_PERIODS 220
#define COOK_ENCODE_ONE_LEADER_POS 100
#define COOK_ENCODE_ONE_OSSIFIER_POS 300
#define COOK_ENCODE_ONE_DATA_BLOCK_POS 800
#define COOK_ENCODE_ONE_TRAILING_GUARD 1000

#define COOK_ENCODE_ARBITRARY_ETHER_PERIODS 420
#define COOK_ENCODE_ARBITRARY_LEADER_POS 100
#define COOK_ENCODE_ARBITRARY_FIRST_OSSIFIER_POS 300
#define COOK_ENCODE_ARBITRARY_OSSIFIER_STRIDE 200
#define COOK_ENCODE_ARBITRARY_DATA_GAP 500
#define COOK_ENCODE_ARBITRARY_ZERO_DATA_BLOCK_POS 800
#define COOK_ENCODE_ARBITRARY_TRAILING_GUARD 1000

#define COOK_ENCODE_PHASE_LEADING_GUARD_PERIODS 64
#define COOK_ENCODE_PHASE_LEADER_TO_OSSIFIER_PERIODS 32
#define COOK_ENCODE_PHASE_MIN_OSSIFIER_STRIDE_PERIODS 64
#define COOK_ENCODE_PHASE_OSSIFIER_TO_DATA_PERIODS 96
#define COOK_ENCODE_PHASE_SYMBOL_STRIDE_PERIODS 64
#define COOK_ENCODE_PHASE_TRAILING_GUARD_PERIODS 64

#define COOK_ENCODE_PHASE_LEADER_WIDTH 704
#define COOK_ENCODE_PHASE_OSSIFIER_WIDTH 234
#define COOK_ENCODE_PHASE_DATA_BLOCK_WIDTH 867

typedef struct {
    size_t total_cells;
    size_t leader_pos;
    size_t first_ossifier_pos;
    size_t ossifier_stride;
    size_t data_pos;
    size_t data_symbol_stride;
} CookPhaseExactLayout;

/*
   The phase-exact packet layout places the initial cyclic-tag tape in the
   data band starting at data_pos. Each symbol occupies one data_symbol_stride
   slot and is emitted as a four-C2 packet. Cook Y is encoded by C2 spacings
   18,18,14 ether tiles; Cook N is encoded by 28,10,14. The output decoder
   searches evolved rows for those C2 spacing packets and reads the largest
   packet band as the visible tape window.
*/

static size_t cook_encode_round_up_periods(size_t cell_count) {
    size_t periods = cell_count / (size_t)COOK_ETHER_WIDTH;

    if (cell_count % (size_t)COOK_ETHER_WIDTH != 0) periods++;

    return periods;
}

static int cook_encode_add_size(size_t left, size_t right, size_t *out) {
    if (left > ((size_t)-1) - right) return 0;

    *out = left + right;
    return 1;
}

static int cook_encode_mul_size(size_t left, size_t right, size_t *out) {
    if (left != 0 && right > ((size_t)-1) / left) return 0;

    *out = left * right;
    return 1;
}

static int cook_encode_validate(const CyclicTagInput *ct) {
    if (ct == NULL) return 0;
    if (ct->tape_len > 0 && ct->initial_tape == NULL) return 0;
    if (ct->num_productions == 0) return 1;
    if (ct->productions == NULL || ct->prod_lens == NULL) return 0;

    for (size_t i = 0; i < ct->num_productions; i++) {
        size_t width = 0;

        if (ct->prod_lens[i] > 0 && ct->productions[i] == NULL) return 0;
        if (!cook_encode_mul_size(ct->prod_lens[i],
                                  COOK_OSSIFIER_WIDTH_PER_BIT,
                                  &width)) {
            return 0;
        }
    }

    return 1;
}

static int cook_phase_cells_from_periods(size_t periods, size_t *out) {
    return cook_encode_mul_size(periods, (size_t)COOK_ETHER_WIDTH, out);
}

static int cook_phase_round_up_ether_width(size_t in, size_t *out) {
    return round_up_ether_width(in, out) == 0;
}

static int cook_encode_phase_exact_layout(const CyclicTagInput *ct,
                                          CookPhaseExactLayout *layout) {
    size_t leading_guard = 0;
    size_t leader_gap = 0;
    size_t min_ossifier_stride = 0;
    size_t production_region_width = 0;
    size_t ossifier_to_data = 0;
    size_t data_symbol_stride = 0;
    size_t trailing_guard = 0;
    size_t leader_end = 0;
    size_t first_ossifier_pos = 0;
    size_t ossifier_stride = 0;
    size_t ossifier_region_end = 0;
    size_t data_pos = 0;
    size_t data_width = 0;
    size_t structure_end = 0;
    size_t required = 0;

    if (layout == NULL) return 0;
    if (!cook_phase_cells_from_periods(COOK_ENCODE_PHASE_LEADING_GUARD_PERIODS,
                                       &leading_guard)) {
        return 0;
    }
    if (!cook_phase_cells_from_periods(COOK_ENCODE_PHASE_LEADER_TO_OSSIFIER_PERIODS,
                                       &leader_gap)) {
        return 0;
    }
    if (!cook_phase_cells_from_periods(COOK_ENCODE_PHASE_MIN_OSSIFIER_STRIDE_PERIODS,
                                       &min_ossifier_stride)) {
        return 0;
    }
    if (!cook_phase_cells_from_periods(COOK_ENCODE_PHASE_OSSIFIER_TO_DATA_PERIODS,
                                       &ossifier_to_data)) {
        return 0;
    }
    if (!cook_phase_cells_from_periods(COOK_ENCODE_PHASE_SYMBOL_STRIDE_PERIODS,
                                       &data_symbol_stride)) {
        return 0;
    }
    if (!cook_phase_cells_from_periods(COOK_ENCODE_PHASE_TRAILING_GUARD_PERIODS,
                                       &trailing_guard)) {
        return 0;
    }

    for (size_t i = 0; i < ct->num_productions; i++) {
        size_t production_width = 0;

        (void)ct->prod_lens[i];
        production_width = COOK_ENCODE_PHASE_OSSIFIER_WIDTH;
        if (production_region_width < production_width) {
            production_region_width = production_width;
        }
    }
    ossifier_stride = min_ossifier_stride;
    if (production_region_width > ossifier_stride) {
        if (!cook_phase_round_up_ether_width(production_region_width,
                                             &ossifier_stride)) {
            return 0;
        }
        if (!cook_encode_add_size(ossifier_stride,
                                  min_ossifier_stride,
                                  &ossifier_stride)) {
            return 0;
        }
    }

    if (!cook_encode_add_size(leading_guard,
                              COOK_ENCODE_PHASE_LEADER_WIDTH,
                              &leader_end)) {
        return 0;
    }
    if (!cook_encode_add_size(leader_end, leader_gap, &first_ossifier_pos)) {
        return 0;
    }
    if (!cook_phase_round_up_ether_width(first_ossifier_pos,
                                         &first_ossifier_pos)) {
        return 0;
    }

    if (ct->num_productions == 0) {
        ossifier_region_end = first_ossifier_pos;
    } else {
        size_t span_count = ct->num_productions - 1;
        size_t ossifier_span = 0;
        size_t last_ossifier_pos = 0;

        if (!cook_encode_mul_size(span_count,
                                  ossifier_stride,
                                  &ossifier_span)) {
            return 0;
        }
        if (!cook_encode_add_size(first_ossifier_pos,
                                  ossifier_span,
                                  &last_ossifier_pos)) {
            return 0;
        }
        if (!cook_encode_add_size(last_ossifier_pos,
                                  production_region_width,
                                  &ossifier_region_end)) {
            return 0;
        }
    }

    if (!cook_encode_add_size(ossifier_region_end,
                              ossifier_to_data,
                              &data_pos)) {
        return 0;
    }
    if (!cook_phase_round_up_ether_width(data_pos, &data_pos)) return 0;

    if (ct->tape_len > 0) {
        size_t symbol_span_count = ct->tape_len - 1;
        size_t symbol_span = 0;

        if (!cook_encode_mul_size(symbol_span_count,
                                  data_symbol_stride,
                                  &symbol_span)) {
            return 0;
        }
        if (!cook_encode_add_size(symbol_span,
                                  COOK_ENCODE_PHASE_DATA_BLOCK_WIDTH,
                                  &data_width)) {
            return 0;
        }
    }

    structure_end = data_pos;
    if (data_width > 0 &&
        !cook_encode_add_size(data_pos, data_width, &structure_end)) {
        return 0;
    }
    if (!cook_encode_add_size(structure_end, trailing_guard, &required)) {
        return 0;
    }
    if (!cook_phase_round_up_ether_width(required, &required)) return 0;

    layout->total_cells = required;
    layout->leader_pos = leading_guard;
    layout->first_ossifier_pos = first_ossifier_pos;
    layout->ossifier_stride = ossifier_stride;
    layout->data_pos = data_pos;
    layout->data_symbol_stride = data_symbol_stride;
    return 1;
}

static int cook_encode_phase_exact_compose(const CyclicTagInput *ct,
                                           const CookPhaseExactLayout *layout,
                                           uint8_t *out) {
    int rc = COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;

    cook_ether_emit(out, layout->total_cells / (size_t)COOK_ETHER_WIDTH);

    rc = cook_leader_emit_phase_exact(out,
                                      layout->leader_pos,
                                      layout->total_cells);
    if (rc != COOK_LEADER_PHASE_EXACT_OK) {
        return COOK_ENCODE_PHASE_EXACT_CATALOG_MISSING;
    }

    for (size_t i = 0; i < ct->num_productions; i++) {
        size_t pos = layout->first_ossifier_pos +
            (i * layout->ossifier_stride);

        rc = cook_ossifier_emit_phase_exact(out,
                                            pos,
                                            layout->total_cells,
                                            ct->productions[i],
                                            ct->prod_lens[i]);
        if (rc != COOK_OSSIFIER_PHASE_EXACT_OK) {
            return COOK_ENCODE_PHASE_EXACT_CATALOG_MISSING;
        }
    }

    for (size_t i = 0; i < ct->tape_len; i++) {
        size_t pos = layout->data_pos + (i * layout->data_symbol_stride);

        rc = cook_data_block_emit_phase_exact(out,
                                              pos,
                                              layout->total_cells,
                                              ct->initial_tape + i,
                                              1);
        if (rc != COOK_DATA_BLOCK_PHASE_EXACT_OK) {
            return COOK_ENCODE_PHASE_EXACT_CATALOG_MISSING;
        }
    }

    return COOK_ENCODE_PHASE_EXACT_OK;
}

static int cook_encode_arbitrary_layout(const CyclicTagInput *ct,
                                        size_t *required_out,
                                        size_t *data_pos_out) {
    size_t structure_end = COOK_ENCODE_ARBITRARY_LEADER_POS;
    size_t leader_end = 0;
    size_t ossifier_pos = COOK_ENCODE_ARBITRARY_FIRST_OSSIFIER_POS;
    size_t data_pos = COOK_ENCODE_ARBITRARY_ZERO_DATA_BLOCK_POS;
    size_t data_width = 0;
    size_t required = 0;
    size_t periods = 0;
    size_t min_required =
        COOK_ENCODE_ARBITRARY_ETHER_PERIODS * (size_t)COOK_ETHER_WIDTH;

    if (!cook_encode_add_size(COOK_ENCODE_ARBITRARY_LEADER_POS,
                              COOK_LEADER_WIDTH,
                              &leader_end)) {
        return 0;
    }
    structure_end = leader_end;

    if (ct->num_productions > 0) {
        for (size_t i = 0; i < ct->num_productions; i++) {
            size_t production_width = 0;
            size_t ossifier_end = 0;
            size_t step = COOK_ENCODE_ARBITRARY_OSSIFIER_STRIDE;

            if (!cook_encode_mul_size(ct->prod_lens[i],
                                      COOK_OSSIFIER_WIDTH_PER_BIT,
                                      &production_width)) {
                return 0;
            }
            if (!cook_encode_add_size(ossifier_pos,
                                      production_width,
                                      &ossifier_end)) {
                return 0;
            }
            if (structure_end < ossifier_end) structure_end = ossifier_end;
            if (production_width > COOK_ENCODE_ARBITRARY_OSSIFIER_STRIDE) {
                if (!cook_encode_add_size(production_width,
                                          COOK_ENCODE_ARBITRARY_OSSIFIER_STRIDE,
                                          &step)) {
                    return 0;
                }
            }
            if (!cook_encode_add_size(ossifier_pos, step, &ossifier_pos)) {
                return 0;
            }
        }

        if (!cook_encode_add_size(ossifier_pos,
                                  COOK_ENCODE_ARBITRARY_DATA_GAP,
                                  &data_pos)) {
            return 0;
        }
    }

    if (!cook_encode_mul_size(ct->tape_len,
                              COOK_DATA_BLOCK_WIDTH_PER_BIT,
                              &data_width)) {
        return 0;
    }
    if (ct->tape_len > 0) {
        size_t data_end = 0;

        if (!cook_encode_add_size(data_pos, data_width, &data_end)) return 0;
        if (structure_end < data_end) structure_end = data_end;
    }

    if (!cook_encode_add_size(structure_end,
                              COOK_ENCODE_ARBITRARY_TRAILING_GUARD,
                              &required)) {
        return 0;
    }
    periods = cook_encode_round_up_periods(required);
    if (periods > ((size_t)-1) / (size_t)COOK_ETHER_WIDTH) return 0;
    required = periods * (size_t)COOK_ETHER_WIDTH;
    if (required < min_required) required = min_required;

    *required_out = required;
    *data_pos_out = data_pos;
    return 1;
}

static size_t cook_encode_arbitrary(const CyclicTagInput *ct,
                                    uint8_t *out,
                                    size_t out_cap) {
    size_t required = 0;
    size_t data_pos = 0;
    size_t ossifier_pos = COOK_ENCODE_ARBITRARY_FIRST_OSSIFIER_POS;

    if (!cook_encode_arbitrary_layout(ct, &required, &data_pos)) return 0;
    if (out_cap < required) return 0;

    cook_ether_emit(out, required / (size_t)COOK_ETHER_WIDTH);
    cook_leader_emit(out,
                     COOK_ENCODE_ARBITRARY_LEADER_POS,
                     required);

    for (size_t i = 0; i < ct->num_productions; i++) {
        size_t production_width = ct->prod_lens[i] *
            COOK_OSSIFIER_WIDTH_PER_BIT;
        size_t step = COOK_ENCODE_ARBITRARY_OSSIFIER_STRIDE;

        cook_ossifier_emit(out,
                           ossifier_pos,
                           required,
                           ct->productions[i],
                           ct->prod_lens[i]);
        if (production_width > COOK_ENCODE_ARBITRARY_OSSIFIER_STRIDE) {
            step = production_width + COOK_ENCODE_ARBITRARY_OSSIFIER_STRIDE;
        }
        ossifier_pos += step;
    }

    if (ct->tape_len > 0) {
        cook_data_block_emit(out,
                             data_pos,
                             required,
                             ct->initial_tape,
                             ct->tape_len);
    }

    return required;
}

size_t cook_encode(const CyclicTagInput *ct, uint8_t *out, size_t out_cap) {
    size_t required;

    if (ct == NULL || out == NULL) return 0;
    if (!cook_encode_validate(ct)) return 0;

    if (ct->num_productions == 0 && ct->tape_len == 0) {
        required = COOK_ENCODE_EMPTY_ETHER_PERIODS * (size_t)COOK_ETHER_WIDTH;

        if (out_cap < required) return 0;

        cook_ether_emit(out, COOK_ENCODE_EMPTY_ETHER_PERIODS);
        cook_leader_emit(out,
                         COOK_ENCODE_EMPTY_LEADER_POS,
                         required);

        return required;
    }

    if (ct->num_productions == 1) {
        size_t min_required =
            COOK_ENCODE_ONE_ETHER_PERIODS * (size_t)COOK_ETHER_WIDTH;
        size_t production_width = 0;
        size_t data_width = 0;
        size_t structure_end = COOK_ENCODE_ONE_DATA_BLOCK_POS;
        size_t periods = COOK_ENCODE_ONE_ETHER_PERIODS;

        if (ct->prod_lens[0] > ((size_t)-1) / COOK_OSSIFIER_WIDTH_PER_BIT) {
            return 0;
        }
        if (ct->tape_len > ((size_t)-1) / COOK_DATA_BLOCK_WIDTH_PER_BIT) {
            return 0;
        }

        production_width = ct->prod_lens[0] * COOK_OSSIFIER_WIDTH_PER_BIT;
        data_width = ct->tape_len * COOK_DATA_BLOCK_WIDTH_PER_BIT;
        if (production_width > 0 &&
            structure_end < COOK_ENCODE_ONE_OSSIFIER_POS + production_width) {
            structure_end = COOK_ENCODE_ONE_OSSIFIER_POS + production_width;
        }
        if (data_width > 0 &&
            structure_end < COOK_ENCODE_ONE_DATA_BLOCK_POS + data_width) {
            structure_end = COOK_ENCODE_ONE_DATA_BLOCK_POS + data_width;
        }
        if (structure_end > ((size_t)-1) - COOK_ENCODE_ONE_TRAILING_GUARD) {
            return 0;
        }

        required = structure_end + COOK_ENCODE_ONE_TRAILING_GUARD;
        periods = cook_encode_round_up_periods(required);
        if (periods > ((size_t)-1) / (size_t)COOK_ETHER_WIDTH) return 0;
        required = periods * (size_t)COOK_ETHER_WIDTH;
        if (required < min_required) required = min_required;
        if (out_cap < required) return 0;

        cook_ether_emit(out, required / (size_t)COOK_ETHER_WIDTH);
        cook_leader_emit(out,
                         COOK_ENCODE_ONE_LEADER_POS,
                         required);
        cook_ossifier_emit(out,
                           COOK_ENCODE_ONE_OSSIFIER_POS,
                           required,
                           ct->productions[0],
                           ct->prod_lens[0]);
        if (ct->tape_len > 0) {
            cook_data_block_emit(out,
                                 COOK_ENCODE_ONE_DATA_BLOCK_POS,
                                 required,
                                 ct->initial_tape,
                                 ct->tape_len);
        }

        return required;
    }

    return cook_encode_arbitrary(ct, out, out_cap);
}

int cook_encode_phase_exact(const CyclicTagInput *ct,
                            uint8_t *out,
                            size_t out_cap,
                            size_t *written_out) {
    CookPhaseExactLayout layout;

    if (written_out != NULL) *written_out = 0;
    if (ct == NULL || out == NULL || written_out == NULL) {
        return COOK_ENCODE_PHASE_EXACT_INVALID_INPUT;
    }
    if (!cook_encode_validate(ct)) {
        return COOK_ENCODE_PHASE_EXACT_INVALID_INPUT;
    }
    if (!cook_encode_phase_exact_layout(ct, &layout)) {
        return COOK_ENCODE_PHASE_EXACT_LAYOUT_OVERFLOW;
    }
    if (out_cap < layout.total_cells) {
        *written_out = layout.total_cells;
        return COOK_ENCODE_PHASE_EXACT_INSUFFICIENT_BUFFER;
    }

    {
        int rc = cook_encode_phase_exact_compose(ct, &layout, out);

        if (rc == COOK_ENCODE_PHASE_EXACT_OK) {
            *written_out = layout.total_cells;
        } else {
            *written_out = 0;
        }
        return rc;
    }
}
