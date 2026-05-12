#include "cook_encode.h"
#include "cook_construction.h"
#include "cook_leader.h"

#include <stdio.h>

#define COOK_ENCODE_EMPTY_ETHER_PERIODS 50
#define COOK_ENCODE_EMPTY_LEADER_POS 100

size_t cook_encode(const CyclicTagInput *ct, uint8_t *out, size_t out_cap) {
    const size_t required =
        COOK_ENCODE_EMPTY_ETHER_PERIODS * (size_t)COOK_ETHER_WIDTH;

    if (ct == NULL || out == NULL) return 0;

    if (ct->num_productions != 0 || ct->tape_len != 0) {
        fprintf(stderr, "non-empty CT not yet implemented (C3-C5)\n");
        return 0;
    }

    if (out_cap < required) return 0;

    cook_ether_emit(out, COOK_ENCODE_EMPTY_ETHER_PERIODS);
    cook_leader_emit(out,
                     COOK_ENCODE_EMPTY_LEADER_POS,
                     required);

    return required;
}
