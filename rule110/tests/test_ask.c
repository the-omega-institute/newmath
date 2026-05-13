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

static void expected_positional_certificate(const char *input_bits,
                                            char *out,
                                            size_t out_cap) {
    size_t out_pos = 0;
    size_t len = strlen(input_bits);

    assert(len < 64);
    for (size_t i = 0; i < len; i++) {
        if (input_bits[i] != '1') continue;
        assert(out_pos + 7 < out_cap);
        out[out_pos++] = '1';
        for (int bit = 5; bit >= 0; bit--) {
            out[out_pos++] = ((i >> (size_t)bit) & 1u) ? '1' : '0';
        }
    }
    assert(out_pos < out_cap);
    out[out_pos] = '\0';
}

static int append_encoded_event_chars(const uint8_t *event,
                                      size_t event_len,
                                      char *out,
                                      size_t out_cap,
                                      size_t *out_pos) {
    uint8_t encoded[128];
    size_t encoded_len;

    if (event_len * 2 + 2 > sizeof(encoded)) return 0;
    encoded_len = gc_event_encode(event, event_len, encoded, sizeof(encoded));
    if (encoded_len == 0) return 0;
    if (*out_pos + encoded_len >= out_cap) return 0;

    for (size_t i = 0; i < encoded_len; i++) {
        out[(*out_pos)++] = encoded[i] ? '1' : '0';
    }
    out[*out_pos] = '\0';
    return 1;
}

static int build_ask_input(size_t probe,
                           unsigned history_value,
                           size_t history_depth,
                           uint8_t mark,
                           uint8_t evidence,
                           char *out,
                           size_t out_cap) {
    uint8_t probe_event[16];
    uint8_t history_event[16];
    uint8_t mark_event[1];
    uint8_t evidence_event[1];
    size_t out_pos = 0;

    if (probe + 1 > sizeof(probe_event)) return 0;
    if (history_depth > sizeof(history_event)) return 0;

    for (size_t i = 0; i < probe; i++) probe_event[i] = 0;
    probe_event[probe] = 1;
    for (size_t i = 0; i < history_depth; i++) {
        size_t shift = history_depth - 1 - i;
        history_event[i] = (uint8_t)((history_value >> shift) & 1u);
    }
    mark_event[0] = mark;
    evidence_event[0] = evidence;

    out[0] = '\0';
    return append_encoded_event_chars(probe_event, probe + 1, out, out_cap, &out_pos) &&
           append_encoded_event_chars(history_event, history_depth, out, out_cap, &out_pos) &&
           append_encoded_event_chars(mark_event, 1, out, out_cap, &out_pos) &&
           append_encoded_event_chars(evidence_event, 1, out, out_cap, &out_pos);
}

static void assert_ask_algo_ct_case_with_marker(const char *input_bits,
                                                int expected_holds,
                                                const char *expected_marker) {
    MrResult r;

    assert(decode_ask_holds(input_bits) == expected_holds);
    r = mr_run_ct_manifest("manifests/ask/ask_basic.algo.ct",
                           input_bits,
                           expected_marker,
                           strlen(input_bits));
    if (r != MR_PASS) {
        fprintf(stderr, "ask_basic.algo CT FAIL on input=%s: result=%d\n",
                input_bits, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_ask_algo_ct_case(const char *input_bits, int expected_holds) {
    char expected_marker[512];

    expected_positional_certificate(input_bits,
                                    expected_marker,
                                    sizeof(expected_marker));
    assert_ask_algo_ct_case_with_marker(input_bits,
                                        expected_holds,
                                        expected_marker);
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
    assert_ask_algo_ct_case_with_marker("101111011011",
                                        1,
                                        "100000010000101000011100010010001011000111100100010010101001011");
    printf("  ask_basic.algo: 12/12 decoder cases + CT smoke PASS\n");
}

static void test_ask_algo_via_ct_runner(void) {
    struct AskAlgoCase {
        const char *input;
        int holds;
        const char *marker;
    };
    const struct AskAlgoCase manifest_cases[] = {
        {"101111011011", 1, "100000010000101000011100010010001011000111100100010010101001011"},
        {"101101110111011", 1, "10000001000010100001110001011000110100011110010011001010100101110011011001110"},
        {"010111110111011", 1, "10000011000011100010010001011000110100011110010011001010100101110011011001110"},
        {"01011011011011", 1, "100000110000111000100100011010001111001001100101010011001001101"},
        {"00101110011011011", 1, "1000010100010010001011000110100100110010101001100100110110011111010000"},
        {"00010110101011011011", 1, "10000111000101100011010010001001010100110010011011001111101000010100101010011"},
        {"1011111011011", 0, "1000000100001010000111000100100010110001101001000100100110010111001100"},
        {"1011110111011", 0, "1000000100001010000111000100100010110001111001000100100110010111001100"},
        {"01011110111011", 0, "1000001100001110001001000101100011010010001001001100101010011001001101"},
        {"010110110111011", 0, "1000001100001110001001000110100011110010011001010100101110011011001110"},
        {"1111011011", 0, "10000001000001100001010000111000101100011010010001001001"},
        {"10111101101111", 0, "10000001000010100001110001001000101100011110010001001010100101110011001001101"}
    };
    char input[128];
    size_t checked = 0;

    for (size_t i = 0; i < sizeof(manifest_cases) / sizeof(manifest_cases[0]); i++) {
        assert_ask_algo_ct_case_with_marker(manifest_cases[i].input,
                                            manifest_cases[i].holds,
                                            manifest_cases[i].marker);
    }

    for (size_t probe = 0; probe <= 5; probe++) {
        for (size_t depth = 0; depth <= 4; depth++) {
            unsigned history_limit = 1u << depth;
            for (unsigned history_value = 0; history_value < history_limit; history_value++) {
                for (uint8_t mark = 0; mark <= 1; mark++) {
                    for (uint8_t evidence = 0; evidence <= 1; evidence++) {
                        assert(build_ask_input(probe,
                                               history_value,
                                               depth,
                                               mark,
                                               evidence,
                                               input,
                                               sizeof(input)));
                        assert_ask_algo_ct_case(input, decode_ask_holds(input));
                        checked++;
                    }
                }
            }
        }
    }

    printf("  ask_basic.algo CT runner: %zu bounded cases PASS\n", checked + 12);
}

static void pipeline_smoke_test_ask_manifests(void) {
    assert_manifest_smoke("manifests/ask/ask_basic.enum.ct", "101111011011");
    assert_ask_algo_ct_case("101111011011", 1);
    printf("  pipeline_smoke (enum halt-empty + algo certificate): PASS\n");
}

int main(void) {
    printf("== test_ask ==\n");
    test_ask_basic_enum();
    test_ask_basic_algo();
    test_ask_algo_via_ct_runner();
    pipeline_smoke_test_ask_manifests();
    printf("ALL test_ask assertions passed (bounded Ask CT runner + decoder cross-check)\n");
    return 0;
}
