#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int bhist_enum_assert_reflexive(const char *input_bits) {
    size_t in_len = strlen(input_bits);
    uint8_t *in_bytes = (uint8_t *)malloc(in_len);
    if (in_bytes == NULL) return 0;
    for (size_t i = 0; i < in_len; i++) in_bytes[i] = (uint8_t)(input_bits[i] - '0');

    GcBhistDecResult r1 = gc_bhist_decode(in_bytes, in_len, 8192);
    if (r1.status != GC_OK) {
        free(in_bytes);
        free(r1.bhist.choices);
        return 0;
    }

    size_t off = r1.bytes_consumed;
    GcBhistDecResult r2 = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (r2.status != GC_OK) {
        free(in_bytes);
        free(r1.bhist.choices);
        free(r2.bhist.choices);
        return 0;
    }

    int eq = (r1.bhist.depth == r2.bhist.depth) &&
             (r1.bhist.depth == 0 ||
              memcmp(r1.bhist.choices, r2.bhist.choices, r1.bhist.depth) == 0);
    free(in_bytes);
    free(r1.bhist.choices);
    free(r2.bhist.choices);
    return eq;
}

static void test_hsame_refl_enum(void) {
    assert(bhist_enum_assert_reflexive("1111"));
    assert(bhist_enum_assert_reflexive("011011"));
    assert(bhist_enum_assert_reflexive("10111011"));
    assert(bhist_enum_assert_reflexive("0101101011"));
    assert(bhist_enum_assert_reflexive("10010111001011"));
    printf("  hsame_refl.enum: 5/5 cases PASS\n");
}

static void pipeline_smoke_test_hist_manifest(void) {
    MrResult r = mr_run_ct_manifest("manifests/hist/hsame_refl.enum.ct", "1111", "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on manifests/hist/hsame_refl.enum.ct: result=%d\n",
                (int)r);
    }
    assert(r == MR_PASS);
    printf("  pipeline_smoke (hsame_refl.enum, halt-empty in <=200 steps): PASS\n");
}

int main(void) {
    printf("== test_hist ==\n");
    test_hsame_refl_enum();
    pipeline_smoke_test_hist_manifest();
    printf("ALL test_hist assertions passed (5 BHist hsame_refl enum cases)\n");
    return 0;
}
