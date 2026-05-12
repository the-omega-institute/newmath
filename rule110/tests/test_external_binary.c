#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

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

static void free_bhist(BHist *h) {
    free(h->choices);
    h->choices = NULL;
    h->depth = 0;
}

static int bhist_equal(const BHist *a, const BHist *b) {
    return (a->depth == b->depth) &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
}

static int decode_bword_at(const uint8_t *input, size_t input_len,
                           size_t *off, BHist *out) {
    GcBhistDecResult decoded = gc_bhist_decode(input + *off, input_len - *off, 8192);
    if (decoded.status != GC_OK) {
        free(decoded.bhist.choices);
        return 0;
    }
    *off += decoded.bytes_consumed;
    *out = decoded.bhist;
    return 1;
}

static int decode_one_exact(const char *input_bits, BHist *out) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    size_t off = 0;
    int ok = decode_bword_at(bytes, len, &off, out);
    if (ok) ok = (off == len);
    free(bytes);
    return ok;
}

static int decode_three_exact(const char *input_bits, BHist *a, BHist *b, BHist *r) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    size_t off = 0;
    int ok = decode_bword_at(bytes, len, &off, a);
    if (ok) ok = decode_bword_at(bytes, len, &off, b);
    if (ok) ok = decode_bword_at(bytes, len, &off, r);
    if (ok) ok = (off == len);
    free(bytes);
    return ok;
}

static int decode_four_exact(const char *input_bits, BHist *a, BHist *b,
                             BHist *c, BHist *d) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    size_t off = 0;
    int ok = decode_bword_at(bytes, len, &off, a);
    if (ok) ok = decode_bword_at(bytes, len, &off, b);
    if (ok) ok = decode_bword_at(bytes, len, &off, c);
    if (ok) ok = decode_bword_at(bytes, len, &off, d);
    if (ok) ok = (off == len);
    free(bytes);
    return ok;
}

static int bhist_append(const BHist *a, const BHist *b, BHist *out) {
    out->depth = a->depth + b->depth;
    out->choices = NULL;
    if (out->depth == 0) return 1;

    out->choices = (uint8_t *)malloc(out->depth);
    if (out->choices == NULL) {
        out->depth = 0;
        return 0;
    }
    if (b->depth > 0) memcpy(out->choices, b->choices, b->depth);
    if (a->depth > 0) memcpy(out->choices + b->depth, a->choices, a->depth);
    return 1;
}

static int external_append_holds_bhist(const BHist *a, const BHist *b, const BHist *r) {
    BHist computed = {NULL, 0};
    int ok = bhist_append(a, b, &computed);
    int holds = ok && bhist_equal(&computed, r);
    free_bhist(&computed);
    return holds;
}

static int decode_external_append_holds(const char *input_bits) {
    BHist a = {NULL, 0};
    BHist b = {NULL, 0};
    BHist r = {NULL, 0};
    int ok = decode_three_exact(input_bits, &a, &b, &r);
    int holds = ok && external_append_holds_bhist(&a, &b, &r);
    free_bhist(&a);
    free_bhist(&b);
    free_bhist(&r);
    return holds;
}

static int tail_append_equals_result_tail(const BHist *a, const BHist *b,
                                          const BHist *result) {
    if (b->depth == 0 || result->depth == 0) return 0;
    BHist b_tail = {b->choices + 1, b->depth - 1};
    BHist result_tail = {result->choices + 1, result->depth - 1};
    return external_append_holds_bhist(a, &b_tail, &result_tail);
}

static int external_bit0_inversion_check(const char *input_bits) {
    BHist a = {NULL, 0};
    BHist b = {NULL, 0};
    BHist r = {NULL, 0};
    int ok = decode_three_exact(input_bits, &a, &b, &r);
    int theorem_ok = 0;

    if (ok && external_append_holds_bhist(&a, &b, &r) &&
        r.depth > 0 && r.choices[0] == 0) {
        int empty_right_case = (b.depth == 0) && bhist_equal(&a, &r);
        int nonempty_right_case = (b.depth > 0) && (b.choices[0] == 0) &&
                                  tail_append_equals_result_tail(&a, &b, &r);
        theorem_ok = empty_right_case || nonempty_right_case;
    } else {
        theorem_ok = ok;
    }

    free_bhist(&a);
    free_bhist(&b);
    free_bhist(&r);
    return theorem_ok;
}

static int external_bit1_inversion_check(const char *input_bits) {
    BHist a = {NULL, 0};
    BHist b = {NULL, 0};
    BHist r = {NULL, 0};
    int ok = decode_three_exact(input_bits, &a, &b, &r);
    int theorem_ok = 0;

    if (ok && external_append_holds_bhist(&a, &b, &r) &&
        r.depth > 0 && r.choices[0] == 1) {
        int empty_right_case = (b.depth == 0) && bhist_equal(&a, &r);
        int nonempty_right_case = (b.depth > 0) && (b.choices[0] == 1) &&
                                  tail_append_equals_result_tail(&a, &b, &r);
        theorem_ok = empty_right_case || nonempty_right_case;
    } else {
        theorem_ok = ok;
    }

    free_bhist(&a);
    free_bhist(&b);
    free_bhist(&r);
    return theorem_ok;
}

static int external_cross_bit_impossible_check(const char *input_bits) {
    BHist a = {NULL, 0};
    BHist b = {NULL, 0};
    BHist r = {NULL, 0};
    int ok = decode_three_exact(input_bits, &a, &b, &r);
    int impossible_pattern = ok && external_append_holds_bhist(&a, &b, &r) &&
                             r.depth > 0 && b.depth > 0 &&
                             r.choices[0] != b.choices[0];
    free_bhist(&a);
    free_bhist(&b);
    free_bhist(&r);
    return ok && !impossible_pattern;
}

static int external_nil_result_inversion_check(const char *input_bits) {
    BHist a = {NULL, 0};
    BHist b = {NULL, 0};
    BHist r = {NULL, 0};
    int ok = decode_three_exact(input_bits, &a, &b, &r);
    int theorem_ok = 0;
    if (ok && external_append_holds_bhist(&a, &b, &r) && r.depth == 0) {
        theorem_ok = (a.depth == 0) && (b.depth == 0);
    } else {
        theorem_ok = ok;
    }
    free_bhist(&a);
    free_bhist(&b);
    free_bhist(&r);
    return theorem_ok;
}

static int append_results_equal(const BHist *a, const BHist *b,
                                const BHist *c, const BHist *d) {
    BHist left = {NULL, 0};
    BHist right = {NULL, 0};
    int ok = bhist_append(a, b, &left);
    if (ok) ok = bhist_append(c, d, &right);
    int equal = ok && bhist_equal(&left, &right);
    free_bhist(&left);
    free_bhist(&right);
    return equal;
}

static int external_right_cancel_check(const char *input_bits) {
    BHist a = {NULL, 0};
    BHist b = {NULL, 0};
    BHist c = {NULL, 0};
    int ok = 0;
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (bits_to_bytes(input_bits, &bytes, &len)) {
        size_t off = 0;
        ok = decode_bword_at(bytes, len, &off, &a);
        if (ok) ok = decode_bword_at(bytes, len, &off, &b);
        if (ok) ok = decode_bword_at(bytes, len, &off, &c);
        if (ok) ok = (off == len);
        free(bytes);
    }

    int antecedent = ok && append_results_equal(&a, &c, &b, &c);
    int theorem_ok = ok && (!antecedent || bhist_equal(&a, &b));
    free_bhist(&a);
    free_bhist(&b);
    free_bhist(&c);
    return theorem_ok;
}

static int external_left_cancel_check(const char *input_bits) {
    BHist a = {NULL, 0};
    BHist b = {NULL, 0};
    BHist c = {NULL, 0};
    int ok = 0;
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (bits_to_bytes(input_bits, &bytes, &len)) {
        size_t off = 0;
        ok = decode_bword_at(bytes, len, &off, &a);
        if (ok) ok = decode_bword_at(bytes, len, &off, &b);
        if (ok) ok = decode_bword_at(bytes, len, &off, &c);
        if (ok) ok = (off == len);
        free(bytes);
    }

    int antecedent = ok && append_results_equal(&c, &a, &c, &b);
    int theorem_ok = ok && (!antecedent || bhist_equal(&a, &b));
    free_bhist(&a);
    free_bhist(&b);
    free_bhist(&c);
    return theorem_ok;
}

static int external_congruence_check(const char *input_bits) {
    BHist a = {NULL, 0};
    BHist a2 = {NULL, 0};
    BHist b = {NULL, 0};
    BHist b2 = {NULL, 0};
    int ok = decode_four_exact(input_bits, &a, &a2, &b, &b2);
    int antecedent = ok && bhist_equal(&a, &a2) && bhist_equal(&b, &b2);
    int conclusion = ok && append_results_equal(&a, &b, &a2, &b2);
    int theorem_ok = ok && (!antecedent || conclusion);
    free_bhist(&a);
    free_bhist(&a2);
    free_bhist(&b);
    free_bhist(&b2);
    return theorem_ok;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void test_model_reuse(void) {
    BHist empty = {NULL, 0};
    BHist e0 = {NULL, 0};
    BHist e1e0 = {NULL, 0};
    assert(decode_one_exact("11", &empty));
    assert(decode_one_exact("011", &e0));
    assert(decode_one_exact("10011", &e1e0));
    assert(empty.depth == 0);
    assert(e0.depth == 1 && e0.choices[0] == 0);
    assert(e1e0.depth == 2 && e1e0.choices[0] == 1 && e1e0.choices[1] == 0);
    free_bhist(&empty);
    free_bhist(&e0);
    free_bhist(&e1e0);
    printf("  external_model_reuse: 3/3 cases PASS\n");
}

static void assert_external_basic_cases(void) {
    assert(decode_external_append_holds("111111"));
    assert(decode_external_append_holds("01111011"));
    assert(decode_external_append_holds("1110111011"));
    assert(decode_external_append_holds("011101110011"));
    assert(decode_external_append_holds("100110101101010011"));
    assert(decode_external_append_holds("010111001110001011"));
    assert(!decode_external_append_holds("1111011"));
    assert(!decode_external_append_holds("1101111"));
    assert(!decode_external_append_holds("011101101011"));
    assert(!decode_external_append_holds("10011011101011"));
    assert(!decode_external_append_holds("010111001011"));
    assert(!decode_external_append_holds("101111011"));
}

static void test_external_basic_enum(void) {
    assert_external_basic_cases();
    assert_manifest_smoke("manifests/external_binary/external_binary_basic.enum.ct", "111111");
    printf("  external_binary_basic.enum: 12/12 cases PASS\n");
}

static void test_external_basic_algo(void) {
    assert_external_basic_cases();
    assert_manifest_smoke("manifests/external_binary/external_binary_basic.algo.ct", "111111");
    printf("  external_binary_basic.algo: 12/12 cases PASS\n");
}

static void test_external_inversion(void) {
    assert(external_nil_result_inversion_check("111111"));
    assert(external_nil_result_inversion_check("01111011"));
    assert(external_bit0_inversion_check("01111011"));
    assert(external_bit0_inversion_check("11011011"));
    assert(external_bit0_inversion_check("100110101101010011"));
    assert(external_bit1_inversion_check("101111011"));
    assert(external_bit1_inversion_check("1110111011"));
    assert(external_bit1_inversion_check("011101110011"));
    assert(external_cross_bit_impossible_check("011101110011"));
    assert(external_cross_bit_impossible_check("100110101101010011"));
    printf("  external_inversion: 10/10 cases PASS\n");
}

static void test_external_cancellation_and_congruence(void) {
    assert(external_right_cancel_check("0110111011"));
    assert(external_right_cancel_check("01110111011"));
    assert(external_left_cancel_check("01011011101011"));
    assert(external_left_cancel_check("0111011011"));
    assert(external_congruence_check("01101110111011"));
    assert(external_congruence_check("010110101111011"));
    printf("  external_cancellation_congruence: 6/6 cases PASS\n");
}

int main(void) {
    printf("== test_external_binary ==\n");
    test_model_reuse();
    test_external_basic_enum();
    test_external_basic_algo();
    test_external_inversion();
    test_external_cancellation_and_congruence();
    printf("ALL test_external_binary assertions passed (43 ExternalBinary cases + 2-manifest pipeline smoke)\n");
    return 0;
}
