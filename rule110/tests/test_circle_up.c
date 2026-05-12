#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static const char *MODN_ROWS_REFL_EMPTY = "11111111";
static const char *MODN_ROWS_SYMM_UNARY = "1011111111";
static const char *MODN_ROWS_TRANS_TWO = "101011111111";
static const char *MODN_ROWS_CARRIER_VACUOUS = "10110111111";

static const char *MODN_OPS_EMPTY = "1111111111";
static const char *MODN_OPS_UNARY = "101111111111";
static const char *MODN_OPS_TWO_NEG = "10101111111111";
static const char *MODN_OPS_ADD_NEG_VACUOUS = "1011011111111";

static const char *S1_UNIT_EMPTY_COMPONENTS = "101110111010111010111011";
static const char *S1_UNARY_MIXED_COMPONENTS = "100111010111010111010100111010011";
static const char *S1_TWO_TAIL_COMPONENTS = "101011100101110101110010101011010101011";
static const char *S1_LONGER_TAIL_COMPONENTS = "100101110001110101110001001011001001011";

typedef struct {
    BHist *items;
    size_t len;
} BHistSeq;

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

static void free_seq(BHistSeq *seq) {
    for (size_t i = 0; i < seq->len; i++) free_bhist(&seq->items[i]);
    free(seq->items);
    seq->items = NULL;
    seq->len = 0;
}

static int bhist_equal(const BHist *a, const BHist *b) {
    return a->depth == b->depth &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
}

static int bhist_empty(const BHist *h) {
    return h->depth == 0;
}

static int bhist_unary(const BHist *h) {
    for (size_t i = 0; i < h->depth; i++) {
        if (h->choices[i] != 1) return 0;
    }
    return 1;
}

static int bhist_is_e1(const BHist *h) {
    return h->depth > 0 && h->choices[0] == 1;
}

static int bhist_tail_equals(const BHist *h, const BHist *tail) {
    BHist observed;
    if (!bhist_is_e1(h)) return 0;
    observed.choices = h->choices + 1;
    observed.depth = h->depth - 1;
    return bhist_equal(&observed, tail);
}

static int decode_one_bhist(const uint8_t *bytes, size_t len, size_t *off,
                            BHist *out) {
    GcBhistDecResult r = gc_bhist_decode(bytes + *off, len - *off, 8192);
    if (r.status != GC_OK) {
        free_bhist(&r.bhist);
        return 0;
    }
    *off += r.bytes_consumed;
    *out = r.bhist;
    return 1;
}

static int decode_bhists(const char *input_bits, size_t count, BHistSeq *out) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off = 0;
    out->items = NULL;
    out->len = 0;

    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;
    out->items = (BHist *)calloc(count ? count : 1, sizeof(BHist));
    if (out->items == NULL) {
        free(bytes);
        return 0;
    }
    out->len = count;

    for (size_t i = 0; i < count; i++) {
        if (!decode_one_bhist(bytes, len, &off, &out->items[i])) {
            free(bytes);
            free_seq(out);
            return 0;
        }
    }

    if (off != len) {
        free(bytes);
        free_seq(out);
        return 0;
    }
    free(bytes);
    return 1;
}

static BHist bhist_append_value(const BHist *left, const BHist *right) {
    BHist out;
    out.depth = left->depth + right->depth;
    out.choices = NULL;
    if (out.depth == 0) return out;
    out.choices = (uint8_t *)malloc(out.depth);
    assert(out.choices != NULL);
    if (right->depth > 0) memcpy(out.choices, right->choices, right->depth);
    if (left->depth > 0) {
        memcpy(out.choices + right->depth, left->choices, left->depth);
    }
    return out;
}

static int sone_unit_history(const BHist *h) {
    return h->depth == 2 && h->choices[0] == 1 && h->choices[1] == 1;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void check_modn_row_case(const char *input_bits,
                                int expect_carrier_premise,
                                int expect_classifier_premise) {
    BHistSeq seq;
    assert(decode_bhists(input_bits, 4, &seq));
    assert(bhist_unary(&seq.items[0]));

    int h_carrier = bhist_empty(&seq.items[1]);
    int k_carrier = bhist_empty(&seq.items[2]);
    int carrier_premise = h_carrier;
    int classifier_premise = h_carrier && k_carrier &&
                             bhist_equal(&seq.items[1], &seq.items[2]);

    assert(carrier_premise == expect_carrier_premise);
    assert(classifier_premise == expect_classifier_premise);
    if (classifier_premise) {
        assert(bhist_empty(&seq.items[1]));
        assert(bhist_empty(&seq.items[2]));
    }
    assert(bhist_empty(&seq.items[3]));
    free_seq(&seq);
}

static void check_modn_operation_case(const char *input_bits,
                                      int expect_carrier_premise) {
    BHistSeq seq;
    assert(decode_bhists(input_bits, 5, &seq));
    assert(bhist_unary(&seq.items[0]));

    int carrier_premise = bhist_empty(&seq.items[1]) && bhist_empty(&seq.items[2]);
    assert(carrier_premise == expect_carrier_premise);

    assert(bhist_empty(&seq.items[3]));
    assert(bhist_empty(&seq.items[4]));
    free_seq(&seq);
}

static void check_s1_row_case(const char *input_bits) {
    BHistSeq seq;
    BHist expected_tail;
    assert(decode_bhists(input_bits, 5, &seq));

    assert(bhist_is_e1(&seq.items[0]));
    assert(bhist_is_e1(&seq.items[1]));
    assert(sone_unit_history(&seq.items[2]));
    assert(bhist_tail_equals(&seq.items[3], &seq.items[4]));

    BHist dy;
    dy.choices = seq.items[1].choices + 1;
    dy.depth = seq.items[1].depth - 1;
    expected_tail = bhist_append_value(&seq.items[0], &dy);
    assert(bhist_equal(&seq.items[4], &expected_tail));

    free_bhist(&expected_tail);
    free_seq(&seq);
}

static void test_modn_rows_enum(void) {
    check_modn_row_case(MODN_ROWS_REFL_EMPTY, 1, 1);
    check_modn_row_case(MODN_ROWS_SYMM_UNARY, 1, 1);
    check_modn_row_case(MODN_ROWS_TRANS_TWO, 1, 1);
    check_modn_row_case(MODN_ROWS_CARRIER_VACUOUS, 0, 0);
    assert_manifest_smoke("manifests/circle_up/circle_modn_rows.enum.ct",
                          MODN_ROWS_REFL_EMPTY);
    printf("  circle_modn_rows.enum: 4/4 cases PASS\n");
}

static void test_modn_operations_enum(void) {
    check_modn_operation_case(MODN_OPS_EMPTY, 1);
    check_modn_operation_case(MODN_OPS_UNARY, 1);
    check_modn_operation_case(MODN_OPS_TWO_NEG, 1);
    check_modn_operation_case(MODN_OPS_ADD_NEG_VACUOUS, 0);
    assert_manifest_smoke("manifests/circle_up/circle_modn_operations.enum.ct",
                          MODN_OPS_EMPTY);
    printf("  circle_modn_operations.enum: 4/4 cases PASS\n");
}

static void test_s1_rows_enum(void) {
    check_s1_row_case(S1_UNIT_EMPTY_COMPONENTS);
    check_s1_row_case(S1_UNARY_MIXED_COMPONENTS);
    check_s1_row_case(S1_TWO_TAIL_COMPONENTS);
    check_s1_row_case(S1_LONGER_TAIL_COMPONENTS);
    assert_manifest_smoke("manifests/circle_up/circle_s1_rows.enum.ct",
                          S1_UNIT_EMPTY_COMPONENTS);
    printf("  circle_s1_rows.enum: 4/4 cases PASS\n");
}

int main(void) {
    printf("== test_circle_up ==\n");
    test_modn_rows_enum();
    test_modn_operations_enum();
    test_s1_rows_enum();
    printf("ALL test_circle_up assertions passed (12 CircleUp cases + 3 enum-manifest smoke checks)\n");
    return 0;
}
