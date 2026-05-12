#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static int bytes_eq(const uint8_t *a, const uint8_t *b, size_t n) {
    for (size_t i = 0; i < n; i++) if (a[i] != b[i]) return 0;
    return 1;
}

static void test_body_encode_b0(void) {
    uint8_t in[1] = {0};
    uint8_t out[16] = {0};
    size_t n = gc_body_encode(in, 1, out, 16);
    assert(n == 1);
    uint8_t expected[1] = {0};
    assert(bytes_eq(out, expected, 1));
    printf("  body_encode_b0: PASS\n");
}

static void test_body_encode_b1(void) {
    uint8_t in[1] = {1};
    uint8_t out[16] = {0};
    size_t n = gc_body_encode(in, 1, out, 16);
    assert(n == 2);
    uint8_t expected[2] = {1, 0};
    assert(bytes_eq(out, expected, 2));
    printf("  body_encode_b1: PASS\n");
}

static void test_event_encode_b0(void) {
    uint8_t in[1] = {0};
    uint8_t out[16] = {0};
    size_t n = gc_event_encode(in, 1, out, 16);
    /* "0" ++ "11" = "011" */
    assert(n == 3);
    uint8_t expected[3] = {0, 1, 1};
    assert(bytes_eq(out, expected, 3));
    printf("  event_encode_b0: PASS\n");
}

static void test_event_encode_b1(void) {
    uint8_t in[1] = {1};
    uint8_t out[16] = {0};
    size_t n = gc_event_encode(in, 1, out, 16);
    /* "10" ++ "11" = "1011" */
    assert(n == 4);
    uint8_t expected[4] = {1, 0, 1, 1};
    assert(bytes_eq(out, expected, 4));
    printf("  event_encode_b1: PASS\n");
}

static void test_dec_event_roundtrip_b0(void) {
    uint8_t enc[3] = {0, 1, 1};  /* "011" */
    GcDecResult r = gc_dec_event(enc, 3, 64);
    assert(r.status == GC_OK);
    assert(r.event_len == 1);
    assert(r.event[0] == 0);
    assert(r.bytes_consumed == 3);
    free(r.event);
    printf("  dec_event_roundtrip_b0: PASS\n");
}

static void test_dec_event_roundtrip_b1(void) {
    uint8_t enc[4] = {1, 0, 1, 1};  /* "1011" */
    GcDecResult r = gc_dec_event(enc, 4, 64);
    assert(r.status == GC_OK);
    assert(r.event_len == 1);
    assert(r.event[0] == 1);
    assert(r.bytes_consumed == 4);
    free(r.event);
    printf("  dec_event_roundtrip_b1: PASS\n");
}

static void test_dec_event_reject_dangling_one(void) {
    /* "1" with nothing after -- dangling escape */
    uint8_t enc[1] = {1};
    GcDecResult r = gc_dec_event(enc, 1, 64);
    assert(r.status == GC_REJECT_DANGLING_ONE);
    free(r.event);
    printf("  dec_event_reject_dangling_one: PASS\n");
}

static void test_dec_event_reject_unfinished(void) {
    /* "0" with no terminator */
    uint8_t enc[1] = {0};
    GcDecResult r = gc_dec_event(enc, 1, 64);
    assert(r.status == GC_REJECT_UNFINISHED_EVENT);
    free(r.event);
    printf("  dec_event_reject_unfinished: PASS\n");
}

static void test_dec_event_reject_resource_bound(void) {
    /* Long body with no terminator, fuel=0 should fail. */
    uint8_t enc[5] = {0, 0, 0, 0, 0};
    GcDecResult r = gc_dec_event(enc, 5, 0);
    assert(r.status == GC_REJECT_RESOURCE_BOUND_EXCESS);
    free(r.event);
    printf("  dec_event_reject_resource_bound: PASS\n");
}

static void test_dec_event_reject_empty(void) {
    GcDecResult r = gc_dec_event(NULL, 0, 64);
    assert(r.status == GC_REJECT_EMPTY_INPUT_POLICY);
    free(r.event);
    printf("  dec_event_reject_empty: PASS\n");
}

static void test_bhist_encode_empty(void) {
    BHist h = {NULL, 0};
    uint8_t out[16] = {0};
    size_t n = gc_bhist_encode(&h, out, 16);
    uint8_t expected[2] = {1, 1};
    assert(n == 2);
    assert(bytes_eq(out, expected, 2));
    printf("  bhist_encode_empty: PASS\n");
}

static void test_bhist_encode_e0_empty(void) {
    uint8_t choices[1] = {0};
    BHist h = {choices, 1};
    uint8_t out[16] = {0};
    size_t n = gc_bhist_encode(&h, out, 16);
    uint8_t expected[3] = {0, 1, 1};
    assert(n == 3);
    assert(bytes_eq(out, expected, 3));
    printf("  bhist_encode_e0_empty: PASS\n");
}

static void test_bhist_encode_e1_empty(void) {
    uint8_t choices[1] = {1};
    BHist h = {choices, 1};
    uint8_t out[16] = {0};
    size_t n = gc_bhist_encode(&h, out, 16);
    uint8_t expected[4] = {1, 0, 1, 1};
    assert(n == 4);
    assert(bytes_eq(out, expected, 4));
    printf("  bhist_encode_e1_empty: PASS\n");
}

static void test_bhist_encode_depth_3(void) {
    uint8_t choices[3] = {0, 1, 0};
    BHist h = {choices, 3};
    uint8_t out[16] = {0};
    size_t n = gc_bhist_encode(&h, out, 16);
    uint8_t expected[6] = {0, 1, 0, 0, 1, 1};
    assert(n == 6);
    assert(bytes_eq(out, expected, 6));
    printf("  bhist_encode_depth_3: PASS\n");
}

static void test_bhist_encode_depth_10(void) {
    uint8_t choices[10] = {0, 1, 1, 0, 1, 0, 0, 1, 1, 0};
    BHist h = {choices, 10};
    uint8_t out[32] = {0};
    size_t n = gc_bhist_encode(&h, out, 32);
    uint8_t expected[17] = {
        0, 1, 0, 1, 0, 0, 1, 0,
        0, 0, 1, 0, 1, 0, 0, 1,
        1
    };
    assert(n == 17);
    assert(bytes_eq(out, expected, 17));
    printf("  bhist_encode_depth_10: PASS\n");
}

static void test_bhist_encode_depth_100(void) {
    uint8_t choices[100];
    uint8_t out[256] = {0};
    uint8_t expected[152];
    size_t e = 0;

    for (size_t i = 0; i < 100; i++) {
        choices[i] = (uint8_t)(i % 2);
        if (choices[i] == 0) {
            expected[e++] = 0;
        } else {
            expected[e++] = 1;
            expected[e++] = 0;
        }
    }
    expected[e++] = 1;
    expected[e++] = 1;

    BHist h = {choices, 100};
    size_t n = gc_bhist_encode(&h, out, 256);
    assert(e == 152);
    assert(n == e);
    assert(bytes_eq(out, expected, e));
    printf("  bhist_encode_depth_100: PASS\n");
}

static void test_bhist_decode_roundtrip(void) {
    uint8_t choices2[2] = {0, 1};
    uint8_t choices[10] = {1, 0, 1, 1, 0, 0, 1, 0, 1, 0};
    uint8_t out[32] = {0};
    BHist h2 = {choices2, 2};
    BHist h = {choices, 10};

    size_t n2 = gc_bhist_encode(&h2, out, 32);
    GcBhistDecResult r2 = gc_bhist_decode(out, n2, 64);
    assert(r2.status == GC_OK);
    assert(r2.bhist.depth == h2.depth);
    assert(bytes_eq(r2.bhist.choices, h2.choices, h2.depth));
    assert(r2.bytes_consumed == n2);
    free(r2.bhist.choices);

    size_t n = gc_bhist_encode(&h, out, 32);
    GcBhistDecResult r = gc_bhist_decode(out, n, 64);
    assert(r.status == GC_OK);
    assert(r.bhist.depth == h.depth);
    assert(bytes_eq(r.bhist.choices, h.choices, h.depth));
    assert(r.bytes_consumed == n);
    free(r.bhist.choices);
    printf("  bhist_decode_roundtrip: PASS\n");
}

static void test_bhist_decode_reject_unfinished(void) {
    uint8_t enc[4] = {0, 1, 0, 0};
    GcBhistDecResult r = gc_bhist_decode(enc, 4, 64);
    assert(r.status == GC_REJECT_UNFINISHED_EVENT);
    free(r.bhist.choices);
    printf("  bhist_decode_reject_unfinished: PASS\n");
}

int main(void) {
    printf("== test_encoder ==\n");
    test_body_encode_b0();
    test_body_encode_b1();
    test_event_encode_b0();
    test_event_encode_b1();
    test_dec_event_roundtrip_b0();
    test_dec_event_roundtrip_b1();
    test_dec_event_reject_dangling_one();
    test_dec_event_reject_unfinished();
    test_dec_event_reject_resource_bound();
    test_dec_event_reject_empty();
    test_bhist_encode_empty();
    test_bhist_encode_e0_empty();
    test_bhist_encode_e1_empty();
    test_bhist_encode_depth_3();
    test_bhist_encode_depth_10();
    test_bhist_encode_depth_100();
    test_bhist_decode_roundtrip();
    test_bhist_decode_reject_unfinished();
    printf("ALL test_encoder tests passed\n");
    return 0;
}
