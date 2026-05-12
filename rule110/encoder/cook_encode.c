#include "cook_encode.h"
#include "cook_construction.h"
#include "cook_data_block.h"
#include "cook_leader.h"

#include <stdio.h>

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

size_t cook_encode(const CyclicTagInput *ct, uint8_t *out, size_t out_cap) {
    size_t required =
        COOK_ENCODE_EMPTY_ETHER_PERIODS * (size_t)COOK_ETHER_WIDTH;
    size_t tape_width = 0;
    size_t tape_pos = required;

    if (ct == NULL || out == NULL) return 0;

    if (ct->num_productions != 0) {
        fprintf(stderr, "non-empty CT not yet implemented (C3-C5)\n");
        return 0;
    }

    if (ct->tape_len != 0) {
        size_t guard_width;

        if (ct->initial_tape == NULL) return 0;
        if (mul_size(ct->tape_len,
                     COOK_DATA_BLOCK_WIDTH_PER_BIT,
                     &tape_width) != 0) {
            return 0;
        }
        if (mul_size(COOK_ENCODE_TAPE_GUARD_PERIODS,
                     (size_t)COOK_ETHER_WIDTH,
                     &guard_width) != 0) {
            return 0;
        }
        if (add_size(required, guard_width, &tape_pos) != 0) return 0;
        if (add_size(tape_pos, tape_width, &required) != 0) return 0;
        if (add_size(required, guard_width, &required) != 0) return 0;
        if (round_up_ether_width(required, &required) != 0) return 0;
    }

    if (out_cap < required) return 0;

    cook_ether_emit(out, required / (size_t)COOK_ETHER_WIDTH);
    cook_leader_emit(out,
                     COOK_ENCODE_EMPTY_LEADER_POS,
                     required);
    if (ct->tape_len != 0) {
        cook_data_block_emit(out,
                             tape_pos,
                             required,
                             ct->initial_tape,
                             ct->tape_len);
    }

    return required;
}
