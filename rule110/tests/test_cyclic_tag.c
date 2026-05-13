#include "cyclic_tag.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static uint8_t *bits_from_str(const char *s, size_t *out_len) {
    size_t n = strlen(s);
    uint8_t *b = (uint8_t *)malloc(n ? n : 1);
    for (size_t i = 0; i < n; i++) {
        assert(s[i] == '0' || s[i] == '1');
        b[i] = (uint8_t)(s[i] == '1');
    }
    *out_len = n;
    return b;
}

static void test_identity_ct_halts_when_tape_empty(void) {
    /* Zero productions. Tape "1" will not gain anything (no productions to cycle).
       Actually with no productions, we'd divide by zero in pc update. Use one no-op production. */
    /* Instead: single production = empty string. */
    uint8_t empty_prod_storage[1] = {0};
    uint8_t *prods[1] = {empty_prod_storage};
    size_t prod_lens[1] = {0};

    size_t tlen;
    uint8_t *tape = bits_from_str("101", &tlen);
    CtState s;
    int rc = ct_init(&s, prods, prod_lens, 1, tape, tlen, 64);
    assert(rc == 0);

    CtHaltReason h = ct_run_until_halt(&s, 100);
    assert(h == CT_HALT_EMPTY);
    assert(s.tape_len == 0);
    /* 3 steps consume the 3 input bits since productions append nothing. */
    assert(s.steps_taken == 3);

    ct_free(&s);
    free(tape);
    printf("  identity_ct_halts_when_tape_empty: PASS\n");
}

static void test_simple_growth_then_halt(void) {
    /* Two productions: P0 = "10", P1 = "" (empty).
       Tape starts as "1".
       Step 1: head=1, append P0="10", pc=0→1; tape was "1", drop first → "0", then append "10" → "010".
                Wait: append happens THEN drop. Let's be careful.
                Standard Cook semantics: at each step,
                  1. if tape empty → halt
                  2. head = tape[0]
                  3. if head == 1: tape += productions[pc]
                  4. drop tape[0]
                  5. pc = (pc + 1) % num_productions
       So step 1: tape="1", head=1, append "10" → tape="110", drop first → "10", pc=1.
       Step 2: tape="10", head=1, append productions[1]="" → tape="10", drop first → "0", pc=0.
       Step 3: tape="0", head=0, no append, drop first → "", pc=1.
       HALT_EMPTY after step 3. */
    uint8_t p0[2] = {1, 0};
    uint8_t p1_dummy[1] = {0};
    uint8_t *prods[2] = {p0, p1_dummy};
    size_t prod_lens[2] = {2, 0};

    size_t tlen;
    uint8_t *tape = bits_from_str("1", &tlen);
    CtState s;
    int rc = ct_init(&s, prods, prod_lens, 2, tape, tlen, 64);
    assert(rc == 0);

    CtHaltReason h = ct_run_until_halt(&s, 100);
    assert(h == CT_HALT_EMPTY);
    assert(s.steps_taken == 3);

    ct_free(&s);
    free(tape);
    printf("  simple_growth_then_halt: PASS\n");
}

static void test_steplimit_caught(void) {
    /* Infinite loop CT: production = "1", tape = "1".
       Step n: tape always nonempty starting with 1, appends "1", drops first → tape stays "1". */
    uint8_t p0[1] = {1};
    uint8_t *prods[1] = {p0};
    size_t prod_lens[1] = {1};

    size_t tlen;
    uint8_t *tape = bits_from_str("1", &tlen);
    CtState s;
    int rc = ct_init(&s, prods, prod_lens, 1, tape, tlen, 64);
    assert(rc == 0);

    CtHaltReason h = ct_run_until_halt(&s, 50);
    assert(h == CT_HALT_STEPLIMIT);
    assert(s.steps_taken == 50);

    ct_free(&s);
    free(tape);
    printf("  steplimit_caught: PASS\n");
}

int main(void) {
    printf("== test_cyclic_tag ==\n");
    test_identity_ct_halts_when_tape_empty();
    test_simple_growth_then_halt();
    test_steplimit_caught();
    printf("ALL test_cyclic_tag tests passed\n");
    return 0;
}
