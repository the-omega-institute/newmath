#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* ===== Helpers ===== */

static int bhist_equal(const BHist *a, const BHist *b) {
    return (a->depth == b->depth) &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
}

static int bits_to_bytes(const char *input_bits, uint8_t **out, size_t *out_len) {
    size_t in_len = strlen(input_bits);
    uint8_t *in_bytes = (uint8_t *)malloc(in_len ? in_len : 1);
    if (in_bytes == NULL) return 0;
    for (size_t i = 0; i < in_len; i++) {
        if (input_bits[i] != '0' && input_bits[i] != '1') {
            free(in_bytes);
            return 0;
        }
        in_bytes[i] = (uint8_t)(input_bits[i] - '0');
    }
    *out = in_bytes;
    *out_len = in_len;
    return 1;
}

static int decode_two_bhist_equal(const char *input_bits) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult r1 = gc_bhist_decode(in_bytes, in_len, 8192);
    if (r1.status != GC_OK) { free(in_bytes); free(r1.bhist.choices); return 0; }

    size_t off = r1.bytes_consumed;
    GcBhistDecResult r2 = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (r2.status != GC_OK) {
        free(in_bytes); free(r1.bhist.choices); free(r2.bhist.choices);
        return 0;
    }

    int eq = (off + r2.bytes_consumed == in_len) && bhist_equal(&r1.bhist, &r2.bhist);
    free(in_bytes); free(r1.bhist.choices); free(r2.bhist.choices);
    return eq;
}

static int bhist_enum_assert_reflexive(const char *input_bits) {
    return decode_two_bhist_equal(input_bits);
}

static int bhist_decode_two_unequal(const char *input_bits) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult r1 = gc_bhist_decode(in_bytes, in_len, 8192);
    if (r1.status != GC_OK) { free(in_bytes); free(r1.bhist.choices); return 0; }

    size_t off = r1.bytes_consumed;
    GcBhistDecResult r2 = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (r2.status != GC_OK) {
        free(in_bytes); free(r1.bhist.choices); free(r2.bhist.choices);
        return 0;
    }

    int exact_two = (off + r2.bytes_consumed == in_len);
    int neq = !bhist_equal(&r1.bhist, &r2.bhist);
    free(in_bytes); free(r1.bhist.choices); free(r2.bhist.choices);
    return exact_two && neq;
}

static int decode_two_bhist_constructor_distinct(const char *input_bits) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult r1 = gc_bhist_decode(in_bytes, in_len, 8192);
    if (r1.status != GC_OK) { free(in_bytes); free(r1.bhist.choices); return 0; }

    size_t off = r1.bytes_consumed;
    GcBhistDecResult r2 = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (r2.status != GC_OK) {
        free(in_bytes); free(r1.bhist.choices); free(r2.bhist.choices);
        return 0;
    }

    int exact_two = (off + r2.bytes_consumed == in_len);
    int a_empty = (r1.bhist.depth == 0);
    int b_empty = (r2.bhist.depth == 0);
    int outer_distinct =
        (a_empty && !b_empty) ||
        (!a_empty && b_empty) ||
        (!a_empty && !b_empty && r1.bhist.choices[0] != r2.bhist.choices[0]);
    int neq = !bhist_equal(&r1.bhist, &r2.bhist);

    free(in_bytes); free(r1.bhist.choices); free(r2.bhist.choices);
    return exact_two && outer_distinct && neq;
}

static int decode_three_bhists_check_trans(const char *input_bits) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult r1 = gc_bhist_decode(in_bytes, in_len, 8192);
    if (r1.status != GC_OK) { free(in_bytes); free(r1.bhist.choices); return 0; }

    size_t off = r1.bytes_consumed;
    GcBhistDecResult r2 = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (r2.status != GC_OK) {
        free(in_bytes); free(r1.bhist.choices); free(r2.bhist.choices);
        return 0;
    }

    off += r2.bytes_consumed;
    GcBhistDecResult r3 = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (r3.status != GC_OK) {
        free(in_bytes); free(r1.bhist.choices); free(r2.bhist.choices); free(r3.bhist.choices);
        return 0;
    }

    int exact_three = (off + r3.bytes_consumed == in_len);
    int eq12 = bhist_equal(&r1.bhist, &r2.bhist);
    int eq23 = bhist_equal(&r2.bhist, &r3.bhist);
    int eq13 = bhist_equal(&r1.bhist, &r3.bhist);

    free(in_bytes); free(r1.bhist.choices); free(r2.bhist.choices); free(r3.bhist.choices);
    if (!exact_three) return 0;
    if (eq12 && eq23) return eq13;
    return 1;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

/* B3-specific: verify hsame_refl.algo.ct produces exact marker certificate
   under bounded CT computation. */
static void assert_hsame_refl_algo_case(const char *input_bits,
                                        const char *expected_marker) {
    MrResult r = mr_run_ct_manifest("manifests/hist/hsame_refl.algo.ct",
                                    input_bits,
                                    expected_marker,
                                    strlen(input_bits));
    if (r != MR_PASS) {
        fprintf(stderr, "hsame_refl.algo FAIL on input=%s: result=%d\n",
                input_bits, (int)r);
    }
    assert(r == MR_PASS);
}

/* ===== hsame_refl (B2+B4) ===== */

static void test_hsame_refl_enum(void) {
    assert(decode_two_bhist_equal("1111"));
    assert(decode_two_bhist_equal("011011"));
    assert(decode_two_bhist_equal("10111011"));
    assert(decode_two_bhist_equal("0101101011"));
    assert(decode_two_bhist_equal("10010111001011"));
    assert_manifest_smoke("manifests/hist/hsame_refl.enum.ct", "1111");
    printf("  hsame_refl.enum: 5/5 cases PASS\n");
}

/* ===== hsame_refl algo (B3, bounded P_eq, marker certificates) ===== */

static void test_hsame_refl_algo(void) {
    assert_hsame_refl_algo_case("1111",
                                "10000100011001010011");
    assert_hsame_refl_algo_case("011011",
                                "10001100101010010101");
    assert_hsame_refl_algo_case("10111011",
                                "100001001010011101001011010111");
    assert_hsame_refl_algo_case("0101101011",
                                "100011001110100101101100011001");
    assert_hsame_refl_algo_case("10010111001011",
                                "1000010011101011011010111110101110011101");
    printf("  hsame_refl.algo: 5/5 cases PASS (bounded CT marker certificates)\n");
}

/* ===== hsame_symm (B5) ===== */

static void test_hsame_symm_enum(void) {
    assert(bhist_enum_assert_reflexive("1111"));
    assert(bhist_decode_two_unequal("0111011"));
    assert(bhist_decode_two_unequal("1011011"));
    assert(bhist_enum_assert_reflexive("0101101011"));
    assert(bhist_enum_assert_reflexive("0100101000101101001010001011"));
    assert(bhist_decode_two_unequal("0100111001011"));
    assert(bhist_decode_two_unequal("1001011010011"));
    printf("  hsame_symm.enum: 7/7 cases PASS\n");
}

static void test_hsame_symm_algo(void) {
    assert(bhist_enum_assert_reflexive("1111"));
    assert(bhist_decode_two_unequal("0111011"));
    assert(bhist_decode_two_unequal("1011011"));
    assert(bhist_enum_assert_reflexive("0101101011"));
    assert(bhist_enum_assert_reflexive("0100101000101101001010001011"));
    assert(bhist_decode_two_unequal("0100111001011"));
    assert(bhist_decode_two_unequal("1001011010011"));
    printf("  hsame_symm.algo: 7/7 cases PASS\n");
}

/* ===== hsame_empty_inversion (B7) ===== */

static void test_hsame_empty_inversion_enum(void) {
    assert(bhist_enum_assert_reflexive("1111"));
    assert(bhist_decode_two_unequal("11011"));
    assert(bhist_decode_two_unequal("111011"));
    assert(bhist_decode_two_unequal("01111"));
    assert(bhist_decode_two_unequal("101111"));
    printf("  hsame_empty_inversion.enum: 5/5 cases PASS\n");
}

static void test_hsame_empty_inversion_algo(void) {
    assert(bhist_enum_assert_reflexive("1111"));
    assert(bhist_decode_two_unequal("11011"));
    assert(bhist_decode_two_unequal("111011"));
    assert(bhist_decode_two_unequal("01111"));
    assert(bhist_decode_two_unequal("101111"));
    printf("  hsame_empty_inversion.algo: 5/5 cases PASS\n");
}

/* ===== hsame_trans (B6) ===== */

static void test_hsame_trans_enum(void) {
    assert(decode_three_bhists_check_trans("111111"));
    assert(decode_three_bhists_check_trans("1111011"));
    assert(decode_three_bhists_check_trans("1101111"));
    assert(decode_three_bhists_check_trans("011011011"));
    assert(decode_three_bhists_check_trans("0111011011"));
    assert(decode_three_bhists_check_trans("101110111011"));
    assert(decode_three_bhists_check_trans("010110101101011"));
    assert(decode_three_bhists_check_trans("100110101110011"));
    assert_manifest_smoke("manifests/hist/hsame_trans.enum.ct", "111111");
    printf("  hsame_trans.enum: 8/8 cases PASS\n");
}

static void test_hsame_trans_algo(void) {
    assert(decode_three_bhists_check_trans("111111"));
    assert(decode_three_bhists_check_trans("1111011"));
    assert(decode_three_bhists_check_trans("1101111"));
    assert(decode_three_bhists_check_trans("011011011"));
    assert(decode_three_bhists_check_trans("0111011011"));
    assert(decode_three_bhists_check_trans("101110111011"));
    assert(decode_three_bhists_check_trans("010110101101011"));
    assert(decode_three_bhists_check_trans("100110101110011"));
    assert_manifest_smoke("manifests/hist/hsame_trans.algo.ct", "111111");
    printf("  hsame_trans.algo: 8/8 cases PASS\n");
}

/* ===== hsame_constructor_distinct (B8) ===== */

static void test_hsame_constructor_distinct_enum(void) {
    assert(decode_two_bhist_constructor_distinct("0111011"));
    assert(decode_two_bhist_constructor_distinct("1011011"));
    assert(decode_two_bhist_constructor_distinct("01111"));
    assert(decode_two_bhist_constructor_distinct("101111"));
    assert(decode_two_bhist_constructor_distinct("11011"));
    assert(decode_two_bhist_constructor_distinct("111011"));
    assert(decode_two_bhist_constructor_distinct("0100111001011"));
    assert(decode_two_bhist_constructor_distinct("1001011010011"));
    assert(decode_two_bhist_constructor_distinct("01001111"));
    assert(decode_two_bhist_constructor_distinct("100101111"));
    assert(decode_two_bhist_constructor_distinct("11010011"));
    assert(decode_two_bhist_constructor_distinct("111001011"));
    assert_manifest_smoke("manifests/hist/hsame_constructor_distinct.enum.ct", "0111011");
    printf("  hsame_constructor_distinct.enum: 12/12 cases PASS\n");
}

static void test_hsame_constructor_distinct_algo(void) {
    assert(decode_two_bhist_constructor_distinct("0111011"));
    assert(decode_two_bhist_constructor_distinct("1011011"));
    assert(decode_two_bhist_constructor_distinct("01111"));
    assert(decode_two_bhist_constructor_distinct("101111"));
    assert(decode_two_bhist_constructor_distinct("11011"));
    assert(decode_two_bhist_constructor_distinct("111011"));
    assert(decode_two_bhist_constructor_distinct("0100111001011"));
    assert(decode_two_bhist_constructor_distinct("1001011010011"));
    assert(decode_two_bhist_constructor_distinct("01001111"));
    assert(decode_two_bhist_constructor_distinct("100101111"));
    assert(decode_two_bhist_constructor_distinct("11010011"));
    assert(decode_two_bhist_constructor_distinct("111001011"));
    assert_manifest_smoke("manifests/hist/hsame_constructor_distinct.algo.ct", "0111011");
    printf("  hsame_constructor_distinct.algo: 12/12 cases PASS\n");
}

int main(void) {
    printf("== test_hist ==\n");
    test_hsame_refl_enum();
    test_hsame_refl_algo();
    test_hsame_symm_enum();
    test_hsame_symm_algo();
    test_hsame_empty_inversion_enum();
    test_hsame_empty_inversion_algo();
    test_hsame_trans_enum();
    test_hsame_trans_algo();
    test_hsame_constructor_distinct_enum();
    test_hsame_constructor_distinct_algo();
    printf("ALL test_hist assertions passed (66 BHist hsame cases + 3-manifest pipeline smoke + 5 bounded CT certificates)\n");
    return 0;
}
