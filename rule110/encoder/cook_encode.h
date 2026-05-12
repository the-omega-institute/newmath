#ifndef COOK_ENCODE_H
#define COOK_ENCODE_H

#include <stddef.h>
#include <stdint.h>

typedef struct {
    uint8_t **productions;
    size_t *prod_lens;
    size_t num_productions;
    uint8_t *initial_tape;
    size_t tape_len;
} CyclicTagInput;

size_t cook_encode(const CyclicTagInput *ct, uint8_t *out, size_t out_cap);

#endif
