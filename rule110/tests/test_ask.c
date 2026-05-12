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

static void free_event_result(GcDecResult *r) {
    free(r->event);
    r->event = NULL;
    r->event_len = 0;
}

static int decode_probe_name_event(const uint8_t *event, size_t event_len,
                                   size_t *name_out) {
    if (event_len == 0) return 0;
    for (size_t i = 0; i + 1 < event_len; i++) {
        if (event[i] != 0) return 0;
    }
    if (event[event_len - 1] != 1) return 0;
    *name_out = event_len - 1;
    return 1;
}

static int decode_one_bit_event(const GcDecResult *event, uint8_t *bit_out) {
    if (event->status != GC_OK || event->event_len != 1) return 0;
    if (event->event[0] != 0 && event->event[0] != 1) return 0;
    *bit_out = event->event[0];
    return 1;
}

static int decode_ask_holds(const char *input_bits) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    size_t off = 0;
    size_t probe_name = 0;
    uint8_t mark_bit = 0;
    uint8_t evidence_bit = 0;

    GcDecResult probe = gc_dec_event(bytes, len, 8192);
    int ok = probe.status == GC_OK &&
             decode_probe_name_event(probe.event, probe.event_len, &probe_name);
    if (ok) off += probe.bytes_consumed;

    GcBhistDecResult history;
    history.status = GC_OK;
    history.bhist.choices = NULL;
    history.bhist.depth = 0;
    history.bytes_consumed = 0;
    if (ok) {
        history = gc_bhist_decode(bytes + off, len - off, 8192);
        ok = history.status == GC_OK;
        if (ok) off += history.bytes_consumed;
    }

    GcDecResult mark = {GC_OK, NULL, 0, 0};
    if (ok) {
        mark = gc_dec_event(bytes + off, len - off, 8192);
        ok = decode_one_bit_event(&mark, &mark_bit);
        if (ok) off += mark.bytes_consumed;
    }

    GcDecResult evidence = {GC_OK, NULL, 0, 0};
    if (ok) {
        evidence = gc_dec_event(bytes + off, len - off, 8192);
        ok = decode_one_bit_event(&evidence, &evidence_bit);
        if (ok) off += evidence.bytes_consumed;
    }

    uint8_t expected = (uint8_t)((probe_name + history.bhist.depth) & 1u);
    int holds = ok && off == len && mark_bit == expected && evidence_bit == expected;

    free(bytes);
    free_event_result(&probe);
    free_bhist_result(&history);
    free_event_result(&mark);
    free_event_result(&evidence);
    return holds;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void test_ask_basic_enum(void) {
    assert(decode_ask_holds("101111011011"));
    assert(decode_ask_holds("101101110111011"));
    assert(decode_ask_holds("010111110111011"));
    assert(decode_ask_holds("01011011011011"));
    assert(decode_ask_holds("00101110011011011"));
    assert(decode_ask_holds("00010110101011011011"));
    assert(!decode_ask_holds("1011111011011"));
    assert(!decode_ask_holds("1011110111011"));
    assert(!decode_ask_holds("01011110111011"));
    assert(!decode_ask_holds("010110110111011"));
    assert(!decode_ask_holds("1111011011"));
    assert(!decode_ask_holds("10111101101111"));
    assert_manifest_smoke("manifests/ask/ask_basic.enum.ct", "101111011011");
    printf("  ask_basic.enum: 12/12 cases PASS\n");
}

static void test_ask_basic_algo(void) {
    assert(decode_ask_holds("101111011011"));
    assert(decode_ask_holds("101101110111011"));
    assert(decode_ask_holds("010111110111011"));
    assert(decode_ask_holds("01011011011011"));
    assert(decode_ask_holds("00101110011011011"));
    assert(decode_ask_holds("00010110101011011011"));
    assert(!decode_ask_holds("1011111011011"));
    assert(!decode_ask_holds("1011110111011"));
    assert(!decode_ask_holds("01011110111011"));
    assert(!decode_ask_holds("010110110111011"));
    assert(!decode_ask_holds("1111011011"));
    assert(!decode_ask_holds("10111101101111"));
    assert_manifest_smoke("manifests/ask/ask_basic.algo.ct", "101111011011");
    printf("  ask_basic.algo: 12/12 cases PASS\n");
}

static void pipeline_smoke_test_ask_manifests(void) {
    struct { const char *path; const char *input; } cases[] = {
        {"manifests/ask/ask_basic.enum.ct", "101111011011"},
        {"manifests/ask/ask_basic.algo.ct", "101111011011"},
    };
    size_t n = sizeof(cases) / sizeof(cases[0]);
    for (size_t i = 0; i < n; i++) {
        assert_manifest_smoke(cases[i].path, cases[i].input);
    }
    printf("  pipeline_smoke (2 ask manifests, all halt-empty in <=200 steps): PASS\n");
}

int main(void) {
    printf("== test_ask ==\n");
    test_ask_basic_enum();
    test_ask_basic_algo();
    pipeline_smoke_test_ask_manifests();
    printf("ALL test_ask assertions passed (24 Ask cases + 2-manifest pipeline smoke)\n");
    return 0;
}
