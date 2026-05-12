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

static int mul_size(size_t a, size_t b, size_t *out) {
    if (a != 0 && b > ((size_t)-1) / a) return -1;
    *out = a * b;
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
