#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

#define FOLD_FIELD_COUNT 9

static const char *FLOW_ALL_EMPTY =
    "011111001111101001111101010011111010101001111101010101001111"
    "101010101010011111010101010101001111101010101010101001111";

static const char *FLOW_MIXED =
    "011011100111011101001101011101010011100111010101001111"
    "101010101001110101110101010101001100111010101010101001110111"
    "010101010101010011011";

static const char *FLOW_UNARY_LADDER =
    "011111001110111010011101011101010011101010111010101001111"
    "101010101001110111010101010100111010111010101010101001110101011"
    "10101010101010100111010101011";

static const char *FLOW_MIXED_NAME_DIFF =
    "011011100111011101001101011101010011100111010101001111"
    "101010101001110101110101010101001100111010101010101001110111"
    "0101010101010100111011";

typedef struct {
    BHist fields[FOLD_FIELD_COUNT];
} FoldKernelFixture;

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

static void fold_fixture_init(FoldKernelFixture *k) {
    for (size_t i = 0; i < FOLD_FIELD_COUNT; i++) {
        k->fields[i].choices = NULL;
        k->fields[i].depth = 0;
    }
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
    r->bytes_consumed = 0;
}

static void fold_fixture_free(FoldKernelFixture *k) {
    for (size_t i = 0; i < FOLD_FIELD_COUNT; i++) free_bhist(&k->fields[i]);
}

static int bhist_equal(const BHist *a, const BHist *b) {
    return a->depth == b->depth &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
}

static int fold_fields_equal(const FoldKernelFixture *a,
                             const FoldKernelFixture *b) {
    for (size_t i = 0; i < FOLD_FIELD_COUNT; i++) {
        if (!bhist_equal(&a->fields[i], &b->fields[i])) return 0;
    }
    return 1;
}

static int event_is_fold_tag(const GcDecResult *r, size_t tag_index) {
    if (r->event_len != tag_index + 1) return 0;
    for (size_t i = 0; i < tag_index; i++) {
        if (r->event[i] != 1) return 0;
    }
    return r->event[tag_index] == 0;
}

static int event_marks_are_binary(const GcDecResult *r) {
    for (size_t i = 0; i < r->event_len; i++) {
        if (r->event[i] != 0 && r->event[i] != 1) return 0;
    }
    return 1;
}

static int decode_next_event(const uint8_t *bytes,
                             size_t len,
                             size_t *off,
                             GcDecResult *out) {
    *out = gc_dec_event(bytes + *off, len - *off, 8192);
    if (out->status != GC_OK) return 0;
    *off += out->bytes_consumed;
    return 1;
}

static int decode_fold_flow_from_bytes(const uint8_t *bytes,
                                       size_t len,
                                       size_t *off,
                                       FoldKernelFixture *out) {
    fold_fixture_init(out);
    for (size_t i = 0; i < FOLD_FIELD_COUNT; i++) {
        GcDecResult tag;
        GcDecResult field;

        if (!decode_next_event(bytes, len, off, &tag)) {
            free_event_result(&tag);
            fold_fixture_free(out);
            return 0;
        }
        if (!event_is_fold_tag(&tag, i) || !event_marks_are_binary(&tag)) {
            free_event_result(&tag);
            fold_fixture_free(out);
            return 0;
        }
        free_event_result(&tag);

        if (!decode_next_event(bytes, len, off, &field)) {
            free_event_result(&field);
            fold_fixture_free(out);
            return 0;
        }
        if (!event_marks_are_binary(&field)) {
            free_event_result(&field);
            fold_fixture_free(out);
            return 0;
        }
        out->fields[i].choices = field.event;
        out->fields[i].depth = field.event_len;
    }
    return 1;
}

static int decode_fold_flow_exact(const char *input_bits, FoldKernelFixture *out) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off = 0;
    int ok;

    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;
    ok = decode_fold_flow_from_bytes(bytes, len, &off, out) && off == len;
    if (!ok) fold_fixture_free(out);
    free(bytes);
    return ok;
}

static size_t append_event_bits(char *out,
                                size_t off,
                                size_t out_cap,
                                const uint8_t *event,
                                size_t event_len) {
    for (size_t i = 0; i < event_len; i++) {
        if (event[i] == 0) {
            if (off + 1 >= out_cap) return 0;
            out[off++] = '0';
        } else if (event[i] == 1) {
            if (off + 2 >= out_cap) return 0;
            out[off++] = '1';
            out[off++] = '0';
        } else {
            return 0;
        }
    }
    if (off + 2 >= out_cap) return 0;
    out[off++] = '1';
    out[off++] = '1';
    out[off] = '\0';
    return off;
}

static size_t append_fold_tag(char *out,
                              size_t off,
                              size_t out_cap,
                              size_t tag_index) {
    uint8_t tag[FOLD_FIELD_COUNT + 1];
    for (size_t i = 0; i < tag_index; i++) tag[i] = 1;
    tag[tag_index] = 0;
    return append_event_bits(out, off, out_cap, tag, tag_index + 1);
}

static int canonical_fold_bits(const FoldKernelFixture *k,
                               char *out,
                               size_t out_cap) {
    size_t off = 0;
    if (out_cap == 0) return 0;
    out[0] = '\0';
    for (size_t i = 0; i < FOLD_FIELD_COUNT; i++) {
        off = append_fold_tag(out, off, out_cap, i);
        if (off == 0) return 0;
        off = append_event_bits(out, off, out_cap,
                                k->fields[i].choices,
                                k->fields[i].depth);
        if (off == 0) return 0;
    }
    return 1;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 300);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void check_round_trip_flow(const char *input_bits) {
    FoldKernelFixture k;
    char canonical[512];

    assert(decode_fold_flow_exact(input_bits, &k));
    assert(canonical_fold_bits(&k, canonical, sizeof(canonical)));
    assert(strcmp(canonical, input_bits) == 0);
    for (size_t i = 0; i < FOLD_FIELD_COUNT; i++) {
        for (size_t j = 0; j < k.fields[i].depth; j++) {
            assert(k.fields[i].choices[j] == 0 || k.fields[i].choices[j] == 1);
        }
    }
    fold_fixture_free(&k);
}

static void check_tag_layout_flow(const char *input_bits) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off = 0;

    assert(bits_to_bytes(input_bits, &bytes, &len));
    for (size_t i = 0; i < FOLD_FIELD_COUNT; i++) {
        GcDecResult tag;
        GcDecResult field;
        assert(decode_next_event(bytes, len, &off, &tag));
        assert(event_is_fold_tag(&tag, i));
        assert(event_marks_are_binary(&tag));
        free_event_result(&tag);
        assert(decode_next_event(bytes, len, &off, &field));
        assert(event_marks_are_binary(&field));
        free_event_result(&field);
    }
    assert(off == len);
    free(bytes);
}

static void check_injectivity_pair(const char *left_bits,
                                   const char *right_bits,
                                   int expected_equal) {
    char pair[1024];
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off = 0;
    FoldKernelFixture left;
    FoldKernelFixture right;
    char left_canonical[512];
    char right_canonical[512];
    int fields_equal;
    int flows_equal;

    assert(strlen(left_bits) + strlen(right_bits) + 1 < sizeof(pair));
    strcpy(pair, left_bits);
    strcat(pair, right_bits);

    assert(bits_to_bytes(pair, &bytes, &len));
    assert(decode_fold_flow_from_bytes(bytes, len, &off, &left));
    assert(decode_fold_flow_from_bytes(bytes, len, &off, &right));
    assert(off == len);

    assert(canonical_fold_bits(&left, left_canonical, sizeof(left_canonical)));
    assert(canonical_fold_bits(&right, right_canonical, sizeof(right_canonical)));
    fields_equal = fold_fields_equal(&left, &right);
    flows_equal = strcmp(left_canonical, right_canonical) == 0;
    assert(fields_equal == flows_equal);
    assert(fields_equal == expected_equal);

    fold_fixture_free(&left);
    fold_fixture_free(&right);
    free(bytes);
}

static void test_round_trip_enum(void) {
    check_round_trip_flow(FLOW_ALL_EMPTY);
    check_round_trip_flow(FLOW_MIXED);
    check_round_trip_flow(FLOW_UNARY_LADDER);
    assert_manifest_smoke("manifests/fold_up/fold_round_trip.enum.ct",
                          FLOW_ALL_EMPTY);
    printf("  fold_round_trip.enum: 3/3 cases PASS\n");
}

static void test_tag_layout_enum(void) {
    check_tag_layout_flow(FLOW_ALL_EMPTY);
    check_tag_layout_flow(FLOW_MIXED);
    check_tag_layout_flow(FLOW_UNARY_LADDER);
    assert_manifest_smoke("manifests/fold_up/fold_tag_layout.enum.ct",
                          FLOW_MIXED);
    printf("  fold_tag_layout.enum: 3/3 cases PASS\n");
}

static void test_injectivity_enum(void) {
    check_injectivity_pair(FLOW_ALL_EMPTY, FLOW_ALL_EMPTY, 1);
    check_injectivity_pair(FLOW_ALL_EMPTY, FLOW_MIXED, 0);
    check_injectivity_pair(FLOW_MIXED, FLOW_MIXED_NAME_DIFF, 0);
    assert_manifest_smoke("manifests/fold_up/fold_injectivity.enum.ct",
                          FLOW_ALL_EMPTY);
    printf("  fold_injectivity.enum: 3/3 cases PASS\n");
}

int main(void) {
    printf("== test_fold_up ==\n");
    test_round_trip_enum();
    test_tag_layout_enum();
    test_injectivity_enum();
    printf("ALL test_fold_up assertions passed (9 FoldMomentKernelUp cases + 3 enum-manifest smoke checks)\n");
    return 0;
}
