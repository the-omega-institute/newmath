#include "cyclic_tag.h"
#include <stdlib.h>
#include <string.h>

static int tape_grow(CtState *s, size_t needed) {
    if (needed <= s->tape_cap) return 0;
    size_t new_cap = s->tape_cap ? s->tape_cap : 64;
    while (new_cap < needed) new_cap *= 2;
    uint8_t *new_tape = (uint8_t *)realloc(s->tape, new_cap);
    if (!new_tape) return -1;
    s->tape = new_tape;
    s->tape_cap = new_cap;
    return 0;
}

int ct_init(CtState *s, uint8_t **productions, size_t *prod_lens, size_t num_productions,
            const uint8_t *initial_tape, size_t initial_tape_len, size_t reserved_cap) {
    s->productions = productions;
    s->prod_lens = prod_lens;
    s->num_productions = num_productions;
    s->pc = 0;
    s->steps_taken = 0;
    s->tape_cap = reserved_cap > initial_tape_len ? reserved_cap : initial_tape_len + 64;
    s->tape = (uint8_t *)malloc(s->tape_cap ? s->tape_cap : 1);
    if (!s->tape) return -1;
    memcpy(s->tape, initial_tape, initial_tape_len);
    s->tape_len = initial_tape_len;
    return 0;
}

void ct_free(CtState *s) {
    free(s->tape);
    s->tape = NULL;
    s->tape_len = 0;
    s->tape_cap = 0;
}

CtHaltReason ct_run_until_halt(CtState *s, size_t max_steps) {
    if (s->num_productions == 0) {
        /* Undefined; treat as halt to avoid divide-by-zero. */
        return CT_HALT_EMPTY;
    }
    for (size_t step = 0; step < max_steps; step++) {
        if (s->tape_len == 0) return CT_HALT_EMPTY;
        uint8_t head = s->tape[0];
        if (head == 1) {
            size_t pl = s->prod_lens[s->pc];
            if (tape_grow(s, s->tape_len + pl) != 0) return CT_HALT_OOM;
            memcpy(s->tape + s->tape_len, s->productions[s->pc], pl);
            s->tape_len += pl;
        }
        /* Drop tape[0] by shifting left. */
        memmove(s->tape, s->tape + 1, s->tape_len - 1);
        s->tape_len--;
        s->pc = (s->pc + 1) % s->num_productions;
        s->steps_taken++;
    }
    return CT_HALT_STEPLIMIT;
}
