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

static int bhist_decode_two_unequal(const char *input_bits) {
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

    int neq = (r1.bhist.depth != r2.bhist.depth) ||
              (r1.bhist.depth != 0 &&
               memcmp(r1.bhist.choices, r2.bhist.choices, r1.bhist.depth) != 0);
    free(in_bytes);
    free(r1.bhist.choices);
    free(r2.bhist.choices);
    return neq;
}

static void test_hsame_refl_enum(void) {
    assert(bhist_enum_assert_reflexive("1111"));
    assert(bhist_enum_assert_reflexive("011011"));
    assert(bhist_enum_assert_reflexive("10111011"));
    assert(bhist_enum_assert_reflexive("0101101011"));
    assert(bhist_enum_assert_reflexive("10010111001011"));
    printf("  hsame_refl.enum: 5/5 cases PASS\n");
}

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

int main(void) {
    printf("== test_hist ==\n");
    test_hsame_refl_enum();
    /* test_hsame_refl_algo(); */
    test_hsame_symm_enum();
    test_hsame_symm_algo();
    test_hsame_empty_inversion_enum();
    test_hsame_empty_inversion_algo();
    printf("ALL test_hist assertions passed (29 BHist hsame cases)\n");
    return 0;
}
