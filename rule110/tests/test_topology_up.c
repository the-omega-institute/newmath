#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct {
    BHist *items;
    size_t len;
} BHistBundle;

static const char *FINITE_EMPTY_EMPTY_AT_EMPTY = "10101110101111";
static const char *FINITE_SINGLETON_EMPTY_AT_E0 = "011101011101011011";
static const char *FINITE_EMPTY_PAIR_AT_E1 = "1010111011010111010111011";
static const char *FINITE_PAIR_SINGLETON_AT_E0_E1 =
    "01110111010110101110101101011";
static const char *FINITE_SINGLETON_PAIR_AT_EMPTY =
    "10111010110110101110101111";

static const char *CARRIER_EMPTY_EMPTY_LEDGER_EMPTY = "10101110101111";
static const char *CARRIER_SINGLETON_EMPTY_LEDGER_E1 = "0111010111010111011";
static const char *CARRIER_EMPTY_PAIR_LEDGER_E1 =
    "1010111011010111010111011";
static const char *CARRIER_PAIR_SINGLETON_LEDGER_E1_E1 =
    "0111011101011011101011101011";

static const char *TAG_SINGLETON = "111111";
static const char *TAG_FINITE_INTERSECTION = "01101111";
static const char *TAG_BINARY_MEET = "1011101111";
static const char *TAG_ARBITRARY_UNION = "0011001111";
static const char *TAG_BOTTOM = "010110101111";
static const char *TAG_TOP = "100111001111";
static const char *TAG_EMPTY_NOT_E0 = "1101111";
static const char *TAG_E0_NOT_E1 = "011101111";
static const char *TAG_E0_E1_NOT_E1_E0 = "010111001111";

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

static void free_event_result(GcDecResult *r) {
    free(r->event);
    r->event = NULL;
    r->event_len = 0;
}

static void free_bundle(BHistBundle *b) {
    for (size_t i = 0; i < b->len; i++) free_bhist(&b->items[i]);
    free(b->items);
    b->items = NULL;
    b->len = 0;
}

static int bhist_equal(const BHist *a, const BHist *b) {
    return a->depth == b->depth &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
}

static int bhist_is_unary(const BHist *h) {
    for (size_t i = 0; i < h->depth; i++) {
        if (h->choices[i] != 1) return 0;
    }
    return 1;
}

static int event_is_bundle_end(const GcDecResult *r) {
    return r->event_len == 2 && r->event[0] == 1 && r->event[1] == 1;
}

static int bundle_push(BHistBundle *b, const GcDecResult *r) {
    BHist *next = (BHist *)realloc(b->items, (b->len + 1) * sizeof(BHist));
    if (next == NULL) return 0;
    b->items = next;
    b->items[b->len].choices = NULL;
    b->items[b->len].depth = r->event_len;
    if (r->event_len > 0) {
        b->items[b->len].choices = (uint8_t *)malloc(r->event_len);
        if (b->items[b->len].choices == NULL) return 0;
        memcpy(b->items[b->len].choices, r->event, r->event_len);
    }
    b->len++;
    return 1;
}

static int decode_bhist_bundle(const uint8_t *bytes, size_t len, size_t *off,
                               BHistBundle *out) {
    out->items = NULL;
    out->len = 0;
    while (*off < len) {
        GcDecResult r = gc_dec_event(bytes + *off, len - *off, 8192);
        if (r.status != GC_OK) {
            free_event_result(&r);
            free_bundle(out);
            return 0;
        }
        *off += r.bytes_consumed;
        if (event_is_bundle_end(&r)) {
            free_event_result(&r);
            return 1;
        }
        if (!bundle_push(out, &r)) {
            free_event_result(&r);
            free_bundle(out);
            return 0;
        }
        free_event_result(&r);
    }
    free_bundle(out);
    return 0;
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

static int decode_two_bundles_and_hist(const char *input_bits, BHistBundle *left,
                                       BHistBundle *right, BHist *x) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;
    if (!decode_bhist_bundle(bytes, len, &off, left)) {
        free(bytes);
        return 0;
    }
    if (!decode_bhist_bundle(bytes, len, &off, right)) {
        free_bundle(left);
        free(bytes);
        return 0;
    }
    if (!decode_one_bhist(bytes, len, &off, x)) {
        free_bundle(left);
        free_bundle(right);
        free(bytes);
        return 0;
    }
    int exact = (off == len);
    if (!exact) {
        free_bundle(left);
        free_bundle(right);
        free_bhist(x);
    }
    free(bytes);
    return exact;
}

static int decode_three_bhists(const char *input_bits, BHist *a, BHist *b,
                               BHist *ledger) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;
    if (!decode_one_bhist(bytes, len, &off, a) ||
        !decode_one_bhist(bytes, len, &off, b) ||
        !decode_one_bhist(bytes, len, &off, ledger)) {
        free_bhist(a);
        free_bhist(b);
        free_bhist(ledger);
        free(bytes);
        return 0;
    }
    int exact = (off == len);
    if (!exact) {
        free_bhist(a);
        free_bhist(b);
        free_bhist(ledger);
    }
    free(bytes);
    return exact;
}

static int bundle_contains(const BHistBundle *b, const BHist *h) {
    for (size_t i = 0; i < b->len; i++) {
        if (bhist_equal(&b->items[i], h)) return 1;
    }
    return 0;
}

static int fixture_ball(const BHist *i, const BHist *x) {
    if (i->depth == 0) return 1;
    return bhist_equal(i, x) || (bhist_is_unary(i) && bhist_is_unary(x));
}

static int finite_base_neighborhood(const BHistBundle *indices, const BHist *x) {
    for (size_t i = 0; i < indices->len; i++) {
        if (!fixture_ball(&indices->items[i], x)) return 0;
    }
    return 1;
}

static BHistBundle bundle_append_value(const BHistBundle *left,
                                       const BHistBundle *right) {
    BHistBundle out;
    out.items = NULL;
    out.len = left->len + right->len;
    if (out.len == 0) return out;
    out.items = (BHist *)calloc(out.len, sizeof(BHist));
    assert(out.items != NULL);
    for (size_t i = 0; i < left->len; i++) {
        out.items[i].depth = left->items[i].depth;
        if (left->items[i].depth > 0) {
            out.items[i].choices = (uint8_t *)malloc(left->items[i].depth);
            assert(out.items[i].choices != NULL);
            memcpy(out.items[i].choices, left->items[i].choices, left->items[i].depth);
        }
    }
    for (size_t i = 0; i < right->len; i++) {
        size_t j = left->len + i;
        out.items[j].depth = right->items[i].depth;
        if (right->items[i].depth > 0) {
            out.items[j].choices = (uint8_t *)malloc(right->items[i].depth);
            assert(out.items[j].choices != NULL);
            memcpy(out.items[j].choices, right->items[i].choices, right->items[i].depth);
        }
    }
    return out;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void check_finite_base_case(const char *input_bits,
                                   size_t expected_left_len,
                                   size_t expected_right_len) {
    BHistBundle left;
    BHistBundle right;
    BHist app_point;
    assert(decode_two_bundles_and_hist(input_bits, &left, &right, &app_point));
    assert(left.len == expected_left_len);
    assert(right.len == expected_right_len);
    BHistBundle appended = bundle_append_value(&left, &right);
    assert(appended.len == left.len + right.len);
    for (size_t i = 0; i < left.len; i++) assert(bundle_contains(&appended, &left.items[i]));
    for (size_t i = 0; i < right.len; i++) assert(bundle_contains(&appended, &right.items[i]));
    int appended_open = finite_base_neighborhood(&appended, &app_point);
    int split_open = finite_base_neighborhood(&left, &app_point) &&
                     finite_base_neighborhood(&right, &app_point);
    assert(appended_open == split_open);
    free_bundle(&appended);
    free_bundle(&left);
    free_bundle(&right);
    free_bhist(&app_point);
}

static void check_carrier_row_case(const char *input_bits,
                                   size_t expected_left_len,
                                   size_t expected_right_len) {
    BHistBundle left;
    BHistBundle right;
    BHist ledger;
    assert(decode_two_bundles_and_hist(input_bits, &left, &right, &ledger));
    assert(left.len == expected_left_len);
    assert(right.len == expected_right_len);
    assert(bhist_is_unary(&ledger));
    BHistBundle meet = bundle_append_value(&left, &right);
    assert(meet.len == left.len + right.len);
    for (size_t i = 0; i < left.len; i++) assert(bundle_contains(&meet, &left.items[i]));
    for (size_t i = 0; i < right.len; i++) assert(bundle_contains(&meet, &right.items[i]));
    free_bundle(&meet);
    free_bundle(&left);
    free_bundle(&right);
    free_bhist(&ledger);
}

static void check_tag_equal_case(const char *input_bits) {
    BHist tag;
    BHist expected;
    BHist ledger;
    assert(decode_three_bhists(input_bits, &tag, &expected, &ledger));
    assert(bhist_equal(&tag, &expected));
    assert(bhist_is_unary(&ledger));
    free_bhist(&tag);
    free_bhist(&expected);
    free_bhist(&ledger);
}

static void check_tag_distinct_case(const char *input_bits) {
    BHist tag;
    BHist expected;
    BHist ledger;
    assert(decode_three_bhists(input_bits, &tag, &expected, &ledger));
    assert(!bhist_equal(&tag, &expected));
    assert(bhist_is_unary(&ledger));
    free_bhist(&tag);
    free_bhist(&expected);
    free_bhist(&ledger);
}

static void test_finite_base_neighborhood_enum(void) {
    check_finite_base_case(FINITE_EMPTY_EMPTY_AT_EMPTY, 0, 0);
    check_finite_base_case(FINITE_SINGLETON_EMPTY_AT_E0, 1, 0);
    check_finite_base_case(FINITE_EMPTY_PAIR_AT_E1, 0, 2);
    check_finite_base_case(FINITE_PAIR_SINGLETON_AT_E0_E1, 2, 1);
    check_finite_base_case(FINITE_SINGLETON_PAIR_AT_EMPTY, 1, 2);
    assert_manifest_smoke("manifests/topology_up/topology_finite_base_neighborhood.enum.ct",
                          FINITE_EMPTY_EMPTY_AT_EMPTY);
    printf("  topology_finite_base_neighborhood.enum: 5/5 cases PASS\n");
}

static void test_carrier_rows_enum(void) {
    check_carrier_row_case(CARRIER_EMPTY_EMPTY_LEDGER_EMPTY, 0, 0);
    check_carrier_row_case(CARRIER_SINGLETON_EMPTY_LEDGER_E1, 1, 0);
    check_carrier_row_case(CARRIER_EMPTY_PAIR_LEDGER_E1, 0, 2);
    check_carrier_row_case(CARRIER_PAIR_SINGLETON_LEDGER_E1_E1, 2, 1);
    assert_manifest_smoke("manifests/topology_up/topology_carrier_rows.enum.ct",
                          CARRIER_EMPTY_EMPTY_LEDGER_EMPTY);
    printf("  topology_carrier_rows.enum: 4/4 cases PASS\n");
}

static void test_ledger_tags_enum(void) {
    check_tag_equal_case(TAG_SINGLETON);
    check_tag_equal_case(TAG_FINITE_INTERSECTION);
    check_tag_equal_case(TAG_BINARY_MEET);
    check_tag_equal_case(TAG_ARBITRARY_UNION);
    check_tag_equal_case(TAG_BOTTOM);
    check_tag_equal_case(TAG_TOP);
    check_tag_distinct_case(TAG_EMPTY_NOT_E0);
    check_tag_distinct_case(TAG_E0_NOT_E1);
    check_tag_distinct_case(TAG_E0_E1_NOT_E1_E0);
    assert_manifest_smoke("manifests/topology_up/topology_ledger_tags.enum.ct",
                          TAG_SINGLETON);
    printf("  topology_ledger_tags.enum: 9/9 cases PASS\n");
}

int main(void) {
    printf("== test_topology_up ==\n");
    test_finite_base_neighborhood_enum();
    test_carrier_rows_enum();
    test_ledger_tags_enum();
    printf("ALL test_topology_up assertions passed (18 TopologyUp cases + 3 enum-manifest smoke checks)\n");
    return 0;
}
