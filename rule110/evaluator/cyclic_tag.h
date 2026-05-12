#ifndef CYCLIC_TAG_H
#define CYCLIC_TAG_H

#include <stddef.h>
#include <stdint.h>

typedef enum {
    CT_HALT_EMPTY      = 0,  /* tape became empty — natural halt */
    CT_HALT_STEPLIMIT  = 1,  /* hit max_steps */
    CT_HALT_OOM        = 2   /* tape grew past internal cap */
} CtHaltReason;

typedef struct {
    uint8_t  **productions;     /* productions[i] = bit string */
    size_t   *prod_lens;        /* length of each production */
    size_t    num_productions;
    uint8_t  *tape;
    size_t    tape_len;
    size_t    tape_cap;
    size_t    pc;
    size_t    steps_taken;
} CtState;

/* Initialize CtState with a list of productions, an initial tape, and reserved cap. */
int ct_init(CtState *s, uint8_t **productions, size_t *prod_lens, size_t num_productions,
            const uint8_t *initial_tape, size_t initial_tape_len, size_t reserved_cap);

void ct_free(CtState *s);

/* Run until halt or max_steps. Returns one of CtHaltReason. */
CtHaltReason ct_run_until_halt(CtState *s, size_t max_steps);

#endif
