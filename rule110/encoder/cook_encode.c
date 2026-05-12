#include "cook_encode.h"
#include "cook_construction.h"
#include "cook_data_block.h"
#include "cook_leader.h"
#include "cook_ossifier.h"

#include <stdio.h>

#define COOK_ENCODE_EMPTY_ETHER_PERIODS 50
#define COOK_ENCODE_EMPTY_LEADER_POS 100

#define COOK_ENCODE_ONE_ETHER_PERIODS 220
#define COOK_ENCODE_ONE_LEADER_POS 100
#define COOK_ENCODE_ONE_OSSIFIER_POS 300
#define COOK_ENCODE_ONE_DATA_BLOCK_POS 800
#define COOK_ENCODE_ONE_TRAILING_GUARD 1000

static size_t cook_encode_round_up_periods(size_t cell_count) {
    size_t periods = cell_count / (size_t)COOK_ETHER_WIDTH;

    if (cell_count % (size_t)COOK_ETHER_WIDTH != 0) periods++;

    return periods;
}

size_t cook_encode(const CyclicTagInput *ct, uint8_t *out, size_t out_cap) {
    size_t required;

    if (ct == NULL || out == NULL) return 0;

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

        if (ct->productions == NULL || ct->prod_lens == NULL) return 0;
        if (ct->prod_lens[0] > 0 && ct->productions[0] == NULL) return 0;
        if (ct->tape_len > 0 && ct->initial_tape == NULL) return 0;
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

    fprintf(stderr, "cyclic-tag systems with more than 1 production not yet supported (C4)\n");
    return 0;
}
