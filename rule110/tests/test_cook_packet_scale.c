#include "cook_decode.h"
#include "cook_encode.h"
#include "cyclic_tag.h"
#include "rule110.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_PRODUCTIONS 8
#define MAX_PRODUCTION_BITS 3
#define MAX_TAPE_BITS 16
#define MAX_OUTPUT_SYMBOLS 512

typedef struct {
    const char *name;
    size_t num_productions;
    size_t tape_len;
    size_t step_bound;
    uint8_t productions[MAX_PRODUCTIONS][MAX_PRODUCTION_BITS];
    size_t prod_lens[MAX_PRODUCTIONS];
    uint8_t tape[MAX_TAPE_BITS];
} ScaleCase;

typedef struct {
    const char *name;
    int passed;
    int decode_rc;
    char decoded[MAX_OUTPUT_SYMBOLS];
    char expected[MAX_OUTPUT_SYMBOLS];
} ScaleResult;

static int expected_symbols(const ScaleCase *tc,
                            char *out,
                            size_t out_cap) {
    CtState state;
    uint8_t *productions[MAX_PRODUCTIONS];
    size_t prod_lens[MAX_PRODUCTIONS];
    CtHaltReason halt;

    if (tc == NULL || out == NULL || out_cap == 0) return 0;
    for (size_t i = 0; i < tc->num_productions; i++) {
        productions[i] = (uint8_t *)tc->productions[i];
        prod_lens[i] = tc->prod_lens[i];
    }
    if (ct_init(&state,
                productions,
                prod_lens,
                tc->num_productions,
                tc->tape,
                tc->tape_len,
                128) != 0) {
        return 0;
    }
    halt = ct_run_until_halt(&state, tc->tape_len);
    if (halt == CT_HALT_OOM || state.tape_len + 1 > out_cap) {
        ct_free(&state);
        return 0;
    }
    for (size_t i = 0; i < state.tape_len; i++) {
        out[i] = state.tape[i] ? 'Y' : 'N';
    }
    out[state.tape_len] = '\0';
    ct_free(&state);
    return 1;
}

static void run_scale_case(const ScaleCase *tc, ScaleResult *result) {
    uint8_t *productions[MAX_PRODUCTIONS];
    size_t prod_lens[MAX_PRODUCTIONS];
    CyclicTagInput ct;
    uint8_t placeholder = 0;
    uint8_t *cells = NULL;
    size_t written = 0;
    int rc;

    result->name = tc->name;
    result->passed = 0;
    result->decode_rc = COOK_DECODE_NO_OUTPUT;
    result->decoded[0] = '\0';
    result->expected[0] = '\0';

    if (!expected_symbols(tc, result->expected, sizeof(result->expected))) {
        strcpy(result->decoded, "reference-error");
        return;
    }
    for (size_t i = 0; i < tc->num_productions; i++) {
        productions[i] = (uint8_t *)tc->productions[i];
        prod_lens[i] = tc->prod_lens[i];
    }
    ct.productions = productions;
    ct.prod_lens = prod_lens;
    ct.num_productions = tc->num_productions;
    ct.initial_tape = (uint8_t *)tc->tape;
    ct.tape_len = tc->tape_len;

    rc = cook_encode_phase_exact(&ct, &placeholder, 0, &written);
    if (rc != COOK_ENCODE_PHASE_EXACT_INSUFFICIENT_BUFFER || written == 0) {
        result->decode_rc = rc;
        strcpy(result->decoded, "encode-size-error");
        return;
    }
    cells = (uint8_t *)malloc(written);
    if (cells == NULL) {
        strcpy(result->decoded, "alloc-error");
        return;
    }
    rc = cook_encode_phase_exact(&ct, cells, written, &written);
    if (rc != COOK_ENCODE_PHASE_EXACT_OK) {
        result->decode_rc = rc;
        strcpy(result->decoded, "encode-error");
        free(cells);
        return;
    }

    r110_run_n_steps(cells, written, tc->step_bound);
    rc = cook_decode_output(cells,
                            written,
                            result->decoded,
                            sizeof(result->decoded));
    result->decode_rc = rc;
    result->passed =
        rc == COOK_DECODE_OK &&
        strcmp(result->decoded, result->expected) == 0;
    free(cells);
}

static void print_result(const ScaleResult *result) {
    if (result->passed) {
        printf("  %s: PASS\n", result->name);
    } else {
        printf("  %s: FAIL rc=%d decoded=%s expected=%s\n",
               result->name,
               result->decode_rc,
               result->decoded,
               result->expected);
    }
}

int main(void) {
    const ScaleCase cases[] = {
        {
            "scale_2p_2t_1024",
            2,
            2,
            1024,
            {{1, 0, 0}, {1, 0, 0}},
            {2, 1},
            {1, 0}
        },
        {
            "scale_3p_3t_2048",
            3,
            3,
            2048,
            {{1, 0, 0}, {0, 1, 1}, {1, 1, 0}},
            {2, 3, 2},
            {1, 0, 1}
        },
        {
            "scale_4p_4t_4096",
            4,
            4,
            4096,
            {{1, 1, 0}, {0, 0, 1}, {1, 0, 1}, {0, 1, 0}},
            {3, 2, 3, 1},
            {1, 1, 0, 1}
        },
        {
            "scale_5p_5t_8192",
            5,
            5,
            8192,
            {{1, 0, 1}, {1, 1, 0}, {0, 1, 0}, {1, 0, 0}, {0, 1, 1}},
            {3, 2, 1, 2, 3},
            {1, 0, 1, 1, 0}
        },
        {
            "scale_3p_8t_8192",
            3,
            8,
            8192,
            {{1, 1, 0}, {0, 1, 0}, {1, 0, 1}},
            {3, 2, 3},
            {1, 0, 1, 0, 1, 1, 0, 0}
        },
        {
            "scale_2p_16t_16384",
            2,
            16,
            16384,
            {{1, 0, 0}, {0, 1, 0}},
            {2, 2},
            {1, 0, 0, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0}
        }
    };
    const size_t case_count = sizeof(cases) / sizeof(cases[0]);
    ScaleResult results[sizeof(cases) / sizeof(cases[0])];
    const char *frontier = "none";
    size_t failures = 0;

    printf("== test_cook_packet_scale ==\n");
    for (size_t i = 0; i < case_count; i++) {
        run_scale_case(&cases[i], &results[i]);
        if (results[i].passed) {
            frontier = results[i].name;
        } else {
            failures++;
        }
        print_result(&results[i]);
    }
    printf("Scale frontier: largest passing = %s\n", frontier);
    if (failures == 0) {
        printf("ALL test_cook_packet_scale tests passed\n");
        return 0;
    }
    printf("FAIL %zu scale case(s) - last passing frontier reported above\n",
           failures);
    return 1;
}
