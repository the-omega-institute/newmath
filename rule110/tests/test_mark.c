#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <string.h>
#include <stdlib.h>
#include <stdint.h>

/* For enum manifests: verify that input bit-string decodes to two equal events. */
static int enum_assert_reflexive(const char *input_bits) {
    size_t in_len = strlen(input_bits);
    uint8_t *in_bytes = (uint8_t *)malloc(in_len);
    size_t i;

    if (in_bytes == NULL) return 0;
    for (i = 0; i < in_len; i++) in_bytes[i] = (uint8_t)(input_bits[i] - '0');

    GcDecResult r1 = gc_dec_event(in_bytes, in_len, 64);
    if (r1.status != GC_OK) { free(in_bytes); free(r1.event); return 0; }
    size_t off = r1.bytes_consumed;
    GcDecResult r2 = gc_dec_event(in_bytes + off, in_len - off, 64);
    if (r2.status != GC_OK) { free(in_bytes); free(r1.event); free(r2.event); return 0; }

    int eq = (r1.event_len == r2.event_len) &&
             (memcmp(r1.event, r2.event, r1.event_len) == 0);
    free(in_bytes); free(r1.event); free(r2.event);
    return eq;
}

static void test_msame_refl_enum(void) {
    /* Case 1: msame(b0, b0) input = "011011" */
    assert(enum_assert_reflexive("011011"));
    /* Case 2: msame(b1, b1) input = "10111011" */
    assert(enum_assert_reflexive("10111011"));
    printf("  msame_refl.enum: 2/2 cases PASS\n");
}

int main(void) {
    printf("== test_mark ==\n");
    test_msame_refl_enum();
    printf("ALL test_mark assertions passed\n");
    return 0;
}
