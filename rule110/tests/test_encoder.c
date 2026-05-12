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
    printf("ALL test_encoder tests passed\n");
    return 0;
}
