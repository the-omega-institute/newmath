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

static size_t append_bit_chars(char *dst, size_t off, const char *bits, size_t len) {
    for (size_t i = 0; i < len; i++) {
        dst[off++] = bits[i];
    }
    dst[off] = '\0';
    return off;
}

static size_t encode_bhist_bits(const uint8_t *choices,
                                size_t depth,
                                char *out,
                                size_t out_cap) {
    size_t off = 0;

    for (size_t i = 0; i < depth; i++) {
        if (choices[i] == 0) {
            if (off + 1 >= out_cap) return 0;
            out[off++] = '0';
        } else {
            if (off + 2 >= out_cap) return 0;
            out[off++] = '1';
            out[off++] = '0';
        }
    }

    if (off + 2 >= out_cap) return 0;
    out[off++] = '1';
    out[off++] = '1';
    out[off] = '\0';
    return off;
}

static void make_bhist_choices(unsigned value,
                               size_t depth,
                               uint8_t *choices) {
    for (size_t i = 0; i < depth; i++) {
        size_t shift = depth - i - 1;
        choices[i] = (uint8_t)((value >> shift) & 1u);
    }
}

static int build_ext_input(unsigned h_value,
                           size_t h_depth,
                           uint8_t mark,
                           unsigned r_value,
                           size_t r_depth,
                           char *out,
                           size_t out_cap) {
    uint8_t h_choices[8];
    uint8_t r_choices[8];
    uint8_t mark_choice[1];
    char h_bits[32];
    char r_bits[32];
    char mark_bits[8];
    size_t h_len;
    size_t mark_len;
    size_t r_len;
    size_t off = 0;

    make_bhist_choices(h_value, h_depth, h_choices);
    make_bhist_choices(r_value, r_depth, r_choices);
    mark_choice[0] = mark;

    h_len = encode_bhist_bits(h_choices, h_depth, h_bits, sizeof(h_bits));
    mark_len = encode_bhist_bits(mark_choice, 1, mark_bits, sizeof(mark_bits));
    r_len = encode_bhist_bits(r_choices, r_depth, r_bits, sizeof(r_bits));
    if (h_len == 0 || mark_len == 0 || r_len == 0) return 0;
    if (h_len + mark_len + r_len + 1 > out_cap) return 0;

    off = append_bit_chars(out, off, h_bits, h_len);
    off = append_bit_chars(out, off, mark_bits, mark_len);
    append_bit_chars(out, off, r_bits, r_len);
    return 1;
}

static char *ext_algo_certificate(const char *input_bits) {
    size_t input_len = strlen(input_bits);
    size_t ones = 0;
    char *out;
    size_t off = 0;

    assert(input_len <= 64);
    for (size_t i = 0; i < input_len; i++) {
        assert(input_bits[i] == '0' || input_bits[i] == '1');
        if (input_bits[i] == '1') ones++;
    }

    out = (char *)malloc(ones * 7 + 1);
    assert(out != NULL);
    for (size_t i = 0; i < input_len; i++) {
        if (input_bits[i] == '1') {
            out[off++] = '1';
            for (int bit = 5; bit >= 0; bit--) {
                out[off++] = ((i >> (size_t)bit) & 1u) ? '1' : '0';
            }
        }
    }
    out[off] = '\0';
    return out;
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

static int decode_ext_step_holds(const char *input_bits) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult source = gc_bhist_decode(in_bytes, in_len, 8192);
    if (source.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&source);
        return 0;
    }

    size_t off = source.bytes_consumed;
    GcDecResult mark = gc_dec_event(in_bytes + off, in_len - off, 8192);
    if (mark.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&source);
        free_event_result(&mark);
        return 0;
    }

    off += mark.bytes_consumed;
    GcBhistDecResult result = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (result.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&source);
        free_event_result(&mark);
        free_bhist_result(&result);
        return 0;
    }

    int exact_three = (off + result.bytes_consumed == in_len);
    int mark_is_bit = (mark.event_len == 1) && (mark.event[0] == 0 || mark.event[0] == 1);
    int depth_ok = (result.bhist.depth == source.bhist.depth + 1);
    int head_ok = mark_is_bit && depth_ok && result.bhist.choices[0] == mark.event[0];
    int tail_ok = depth_ok &&
                  (source.bhist.depth == 0 ||
                   memcmp(result.bhist.choices + 1,
                          source.bhist.choices,
                          source.bhist.depth) == 0);
    int holds = exact_three && mark_is_bit && depth_ok && head_ok && tail_ok;

    free(in_bytes);
    free_bhist_result(&source);
    free_event_result(&mark);
    free_bhist_result(&result);
    return holds;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_ext_algo_ct_case_with_marker(const char *input_bits,
                                                int expected_holds,
                                                const char *expected_marker) {
    MrResult r;

    assert(decode_ext_step_holds(input_bits) == expected_holds);
    r = mr_run_ct_manifest("manifests/ext/ext_step.algo.ct",
                           input_bits,
                           expected_marker,
                           strlen(input_bits));
    if (r != MR_PASS) {
        fprintf(stderr, "ext_step.algo CT FAIL on input=%s: result=%d\n",
                input_bits, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_ext_algo_ct_case(const char *input_bits, int expected_holds) {
    char *expected = ext_algo_certificate(input_bits);

    assert_ext_algo_ct_case_with_marker(input_bits, expected_holds, expected);
    free(expected);
}

static void test_ext_step_enum(void) {
    assert(decode_ext_step_holds("11011011"));
    assert(decode_ext_step_holds("1110111011"));
    assert(decode_ext_step_holds("0110110011"));
    assert(decode_ext_step_holds("10111011101011"));
    assert(decode_ext_step_holds("01011011001011"));
    assert(!decode_ext_step_holds("1101111"));
    assert(!decode_ext_step_holds("01101110011"));
    assert(!decode_ext_step_holds("1011101101011"));
    assert_manifest_smoke("manifests/ext/ext_step.enum.ct", "11011011");
    printf("  ext_step.enum: 8/8 cases PASS\n");
}

static void test_ext_step_algo(void) {
    assert(decode_ext_step_holds("11011011"));
    assert(decode_ext_step_holds("1110111011"));
    assert(decode_ext_step_holds("0110110011"));
    assert(decode_ext_step_holds("10111011101011"));
    assert(decode_ext_step_holds("01011011001011"));
    assert(!decode_ext_step_holds("1101111"));
    assert(!decode_ext_step_holds("01101110011"));
    assert(!decode_ext_step_holds("1011101101011"));
    assert_ext_algo_ct_case_with_marker("11011011",
                                        1,
                                        "100000010000011000011100010010001101000111");
    printf("  ext_step.algo: 8/8 decoder cases + CT smoke PASS\n");
}

static void test_ext_step_algo_via_ct_runner(void) {
    struct ExtAlgoCase {
        const char *input;
        int holds;
        const char *marker;
    };
    const struct ExtAlgoCase manifest_cases[] = {
        {"11011011", 1, "100000010000011000011100010010001101000111"},
        {"1110111011", 1, "10000001000001100001010001001000101100011010010001001001"},
        {"0110110011", 1, "100000110000101000100100010110010001001001"},
        {"10111011101011", 1, "1000000100001010000111000100100011010001111001000100101010011001001101"},
        {"01011011001011", 1, "10000011000011100010010001101000111100101010011001001101"},
        {"1101111", 0, "100000010000011000011100010010001011000110"},
        {"01101110011", 0, "1000001100001010001001000101100011010010011001010"},
        {"1011101101011", 0, "100000010000101000011100010010001101000111100100110010111001100"}
    };
    const char *malformed_cases[] = {
        "",
        "1",
        "0",
        "110110110",
        "110",
        "111011"
    };
    char input[96];
    size_t checked = 0;

    for (size_t i = 0; i < sizeof(manifest_cases) / sizeof(manifest_cases[0]); i++) {
        assert_ext_algo_ct_case_with_marker(manifest_cases[i].input,
                                            manifest_cases[i].holds,
                                            manifest_cases[i].marker);
    }

    for (size_t h_depth = 0; h_depth <= 3; h_depth++) {
        unsigned h_limit = 1u << h_depth;
        for (unsigned h_value = 0; h_value < h_limit; h_value++) {
            for (uint8_t mark = 0; mark <= 1; mark++) {
                for (size_t r_depth = 0; r_depth <= 4; r_depth++) {
                    unsigned r_limit = 1u << r_depth;
                    for (unsigned r_value = 0; r_value < r_limit; r_value++) {
                        assert(build_ext_input(h_value, h_depth,
                                               mark,
                                               r_value, r_depth,
                                               input, sizeof(input)));
                        assert_ext_algo_ct_case(input, decode_ext_step_holds(input));
                        checked++;
                    }
                }
            }
        }
    }

    for (size_t i = 0; i < sizeof(malformed_cases) / sizeof(malformed_cases[0]); i++) {
        assert_ext_algo_ct_case(malformed_cases[i], 0);
        checked++;
    }

    printf("  ext_step.algo CT runner: %zu bounded cases PASS\n", checked + 8);
}

int main(void) {
    printf("== test_ext ==\n");
    test_ext_step_enum();
    test_ext_step_algo();
    test_ext_step_algo_via_ct_runner();
    printf("ALL test_ext assertions passed (bounded Ext CT runner + decoder cross-check)\n");
    return 0;
}
