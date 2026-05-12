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

#define COOK_ENCODE_PHASE_EXACT_OK 0
#define COOK_ENCODE_PHASE_EXACT_CATALOG_MISSING 1
#define COOK_ENCODE_PHASE_EXACT_INVALID_INPUT 2
#define COOK_ENCODE_PHASE_EXACT_INSUFFICIENT_BUFFER 3
#define COOK_ENCODE_PHASE_EXACT_LAYOUT_OVERFLOW 4

size_t cook_encode(const CyclicTagInput *ct, uint8_t *out, size_t out_cap);
int cook_encode_phase_exact(const CyclicTagInput *ct,
                            uint8_t *out,
                            size_t out_cap,
                            size_t *written_out);

#endif
