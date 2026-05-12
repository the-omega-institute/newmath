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

static void free_bhist_result(GcBhistDecResult *r) {
    free(r->bhist.choices);
    r->bhist.choices = NULL;
    r->bhist.depth = 0;
}

static int bhist_equal(const BHist *a, const BHist *b) {
    return (a->depth == b->depth) &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
}

static int bhist_unary(const BHist *h) {
    for (size_t i = 0; i < h->depth; i++) {
        if (h->choices[i] != 1) return 0;
    }
    return 1;
}

static int decode_unary_holds(const char *input_bits) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult h = gc_bhist_decode(in_bytes, in_len, 8192);
    int ok = (h.status == GC_OK) &&
             (h.bytes_consumed == in_len) &&
             bhist_unary(&h.bhist);

    free(in_bytes);
    free_bhist_result(&h);
    return ok;
}

static int decode_two_bhist_unary_classifier(const char *input_bits) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult h = gc_bhist_decode(in_bytes, in_len, 8192);
    if (h.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&h);
        return 0;
    }

    size_t off = h.bytes_consumed;
    GcBhistDecResult k = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (k.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&h);
        free_bhist_result(&k);
        return 0;
    }

    int ok = (off + k.bytes_consumed == in_len) &&
             bhist_unary(&h.bhist) &&
             bhist_unary(&k.bhist) &&
             bhist_equal(&h.bhist, &k.bhist);

    free(in_bytes);
    free_bhist_result(&h);
    free_bhist_result(&k);
    return ok;
}

static int cont_holds(const BHist *h, const BHist *k, const BHist *r) {
    if (r->depth != h->depth + k->depth) return 0;
    if (k->depth > 0 && memcmp(r->choices, k->choices, k->depth) != 0) return 0;
    if (h->depth > 0 &&
        memcmp(r->choices + k->depth, h->choices, h->depth) != 0) {
        return 0;
    }
    return 1;
}

static int decode_cont_unary_closed(const char *input_bits) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult h = gc_bhist_decode(in_bytes, in_len, 8192);
    if (h.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&h);
        return 0;
    }

    size_t off = h.bytes_consumed;
    GcBhistDecResult k = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (k.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&h);
        free_bhist_result(&k);
        return 0;
    }

    off += k.bytes_consumed;
    GcBhistDecResult r = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (r.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&h);
        free_bhist_result(&k);
        free_bhist_result(&r);
        return 0;
    }

    int exact_three = (off + r.bytes_consumed == in_len);
    int ok = exact_three &&
             bhist_unary(&h.bhist) &&
             bhist_unary(&k.bhist) &&
             cont_holds(&h.bhist, &k.bhist, &r.bhist) &&
             bhist_unary(&r.bhist);

    free(in_bytes);
    free_bhist_result(&h);
    free_bhist_result(&k);
    free_bhist_result(&r);
    return ok;
}

static int decode_unary_e1_result_case(const char *input_bits) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult h = gc_bhist_decode(in_bytes, in_len, 8192);
    if (h.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&h);
        return 0;
    }

    size_t off = h.bytes_consumed;
    GcBhistDecResult k = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (k.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&h);
        free_bhist_result(&k);
        return 0;
    }

    off += k.bytes_consumed;
    GcBhistDecResult r = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (r.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&h);
        free_bhist_result(&k);
        free_bhist_result(&r);
        return 0;
    }

    int exact_three = (off + r.bytes_consumed == in_len);
    int result_e1 = (r.bhist.depth > 0 && r.bhist.choices[0] == 1);
    int empty_k_case = (k.bhist.depth == 0 &&
                        r.bhist.depth == h.bhist.depth + 1 &&
                        result_e1);
    int step_case = (k.bhist.depth > 0 && k.bhist.choices[0] == 1 &&
                     cont_holds(&h.bhist, &k.bhist, &r.bhist));
    int ok = exact_three &&
             bhist_unary(&h.bhist) &&
             bhist_unary(&k.bhist) &&
             cont_holds(&h.bhist, &k.bhist, &r.bhist) &&
             result_e1 &&
             (empty_k_case || step_case);

    free(in_bytes);
    free_bhist_result(&h);
    free_bhist_result(&k);
    free_bhist_result(&r);
    return ok;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_unary_single_cases(void) {
    assert(decode_unary_holds("11"));
    assert(decode_unary_holds("1011"));
    assert(decode_unary_holds("101011"));
    assert(decode_unary_holds("1010101011"));
    assert(!decode_unary_holds("011"));
    assert(!decode_unary_holds("10011"));
    assert(!decode_unary_holds("01011"));
    assert(!decode_unary_holds("1010011011"));
}

static void assert_unary_classifier_cases(void) {
    assert(decode_two_bhist_unary_classifier("1111"));
    assert(decode_two_bhist_unary_classifier("10111011"));
    assert(decode_two_bhist_unary_classifier("1010101110101011"));
    assert(!decode_two_bhist_unary_classifier("1011101011"));
    assert(!decode_two_bhist_unary_classifier("011011"));
}

static void assert_unary_cont_cases(void) {
    assert(decode_cont_unary_closed("111111"));
    assert(decode_cont_unary_closed("1110111011"));
    assert(decode_cont_unary_closed("1011111011"));
    assert(decode_cont_unary_closed("101110101110101011"));
    assert(decode_cont_unary_closed("101011101110101011"));
    assert(decode_unary_e1_result_case("1110111011"));
    assert(decode_unary_e1_result_case("101110101110101011"));
    assert(!decode_cont_unary_closed("011101101011"));
    assert(!decode_cont_unary_closed("101110101110011"));
    assert(!decode_unary_e1_result_case("111111"));
}

static void test_unary_basic_enum(void) {
    assert_unary_single_cases();
    assert_unary_classifier_cases();
    assert_unary_cont_cases();
    assert_manifest_smoke("manifests/unary/unary_basic.enum.ct", "11");
    printf("  unary_basic.enum: semantic cases PASS\n");
}

static void test_unary_basic_algo(void) {
    assert_unary_single_cases();
    assert_unary_classifier_cases();
    assert_unary_cont_cases();
    assert_manifest_smoke("manifests/unary/unary_basic.algo.ct", "11");
    printf("  unary_basic.algo: semantic cases PASS\n");
}

int main(void) {
    printf("== test_unary ==\n");
    test_unary_basic_enum();
    test_unary_basic_algo();
    printf("ALL test_unary assertions passed\n");
    return 0;
}
