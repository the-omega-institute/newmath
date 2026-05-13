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

static int build_cont_input(unsigned h_value,
                            size_t h_depth,
                            unsigned k_value,
                            size_t k_depth,
                            unsigned r_value,
                            size_t r_depth,
                            char *out,
                            size_t out_cap) {
    uint8_t h_choices[4];
    uint8_t k_choices[4];
    uint8_t r_choices[4];
    char h_bits[16];
    char k_bits[16];
    char r_bits[16];
    size_t h_len;
    size_t k_len;
    size_t r_len;
    size_t off = 0;

    make_bhist_choices(h_value, h_depth, h_choices);
    make_bhist_choices(k_value, k_depth, k_choices);
    make_bhist_choices(r_value, r_depth, r_choices);

    h_len = encode_bhist_bits(h_choices, h_depth, h_bits, sizeof(h_bits));
    k_len = encode_bhist_bits(k_choices, k_depth, k_bits, sizeof(k_bits));
    r_len = encode_bhist_bits(r_choices, r_depth, r_bits, sizeof(r_bits));
    if (h_len == 0 || k_len == 0 || r_len == 0) return 0;
    if (h_len + k_len + r_len + 1 > out_cap) return 0;

    off = append_bit_chars(out, off, h_bits, h_len);
    off = append_bit_chars(out, off, k_bits, k_len);
    append_bit_chars(out, off, r_bits, r_len);
    return 1;
}

static void expected_positional_certificate(const char *input_bits,
                                            char *out,
                                            size_t out_cap) {
    size_t off = 0;
    size_t len = strlen(input_bits);

    assert(len <= 32);
    for (size_t i = 0; i < len; i++) {
        if (input_bits[i] == '1') {
            assert(off + 6 < out_cap);
            out[off++] = '1';
            for (int bit = 4; bit >= 0; bit--) {
                out[off++] = ((i >> (size_t)bit) & 1u) ? '1' : '0';
            }
        }
    }
    out[off] = '\0';
}

static void free_bhist_result(GcBhistDecResult *r) {
    free(r->bhist.choices);
    r->bhist.choices = NULL;
    r->bhist.depth = 0;
}

static int decode_cont_holds(const char *input_bits) {
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
    int depth_ok = (r.bhist.depth == h.bhist.depth + k.bhist.depth);
    int prefix_ok = (k.bhist.depth == 0 ||
                     memcmp(r.bhist.choices,
                            k.bhist.choices,
                            k.bhist.depth) == 0);
    int suffix_ok = (h.bhist.depth == 0 ||
                     memcmp(r.bhist.choices + k.bhist.depth,
                            h.bhist.choices,
                            h.bhist.depth) == 0);
    int holds = exact_three && depth_ok && prefix_ok && suffix_ok;

    free(in_bytes);
    free_bhist_result(&h);
    free_bhist_result(&k);
    free_bhist_result(&r);
    return holds;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_cont_algo_ct_case_with_marker(const char *input_bits,
                                                 int expected_holds,
                                                 const char *expected_marker) {
    MrResult r;

    assert(decode_cont_holds(input_bits) == expected_holds);
    r = mr_run_ct_manifest("manifests/cont/cont_basic.algo.ct",
                           input_bits,
                           expected_marker,
                           strlen(input_bits));
    if (r != MR_PASS) {
        fprintf(stderr, "cont_basic.algo CT FAIL on input=%s: result=%d\n",
                input_bits, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_cont_algo_ct_case(const char *input_bits, int expected_holds) {
    char expected_marker[256];

    expected_positional_certificate(input_bits,
                                    expected_marker,
                                    sizeof(expected_marker));
    assert_cont_algo_ct_case_with_marker(input_bits,
                                         expected_holds,
                                         expected_marker);
}

static void assert_cont_basic_cases(void) {
    assert(decode_cont_holds("111111"));
    assert(decode_cont_holds("01111011"));
    assert(decode_cont_holds("1110111011"));
    assert(decode_cont_holds("011101110011"));
    assert(decode_cont_holds("1011010110101011"));
    assert(decode_cont_holds("010111001110001011"));
    assert(!decode_cont_holds("1111011"));
    assert(!decode_cont_holds("1101111"));
    assert(!decode_cont_holds("011101101011"));
    assert(!decode_cont_holds("101101110011"));
}

static void test_cont_basic_enum(void) {
    assert_cont_basic_cases();
    assert_manifest_smoke("manifests/cont/cont_basic.enum.ct", "111111");
    printf("  cont_basic.enum: 10/10 cases PASS\n");
}

static void test_cont_basic_algo(void) {
    assert_cont_basic_cases();
    assert_cont_algo_ct_case_with_marker("111111",
                                         1,
                                         "100000100001100010100011100100100101");
    printf("  cont_basic.algo: 10/10 decoder cases + CT smoke PASS\n");
}

static void test_cont_algo_via_ct_runner(void) {
    struct ContAlgoCase {
        const char *input;
        int holds;
        const char *marker;
    };
    const struct ContAlgoCase manifest_cases[] = {
        {"111111", 1, "100000100001100010100011100100100101"},
        {"01111011", 1, "100001100010100011100100100110100111"},
        {"1110111011", 1, "100000100001100010100100100101100110101000101001"},
        {"011101110011", 1, "100001100010100011100101100110100111101010101011"},
        {"1011010110101011", 1, "100000100010100011100101100111101000101010101100101110101111"},
        {"010111001110001011", 1, "100001100011100100100101101000101001101010101110110000110001"},
        {"1111011", 0, "100000100001100010100011100101100110"},
        {"1101111", 0, "100000100001100011100100100101100110"},
        {"011101101011", 0, "100001100010100011100101100110101000101010101011"},
        {"101101110011", 0, "100000100010100011100101100110100111101010101011"}
    };
    char input[64];
    size_t checked = 0;

    for (size_t i = 0; i < sizeof(manifest_cases) / sizeof(manifest_cases[0]); i++) {
        assert_cont_algo_ct_case_with_marker(manifest_cases[i].input,
                                             manifest_cases[i].holds,
                                             manifest_cases[i].marker);
    }

    for (size_t h_depth = 0; h_depth <= 2; h_depth++) {
        unsigned h_limit = 1u << h_depth;
        for (unsigned h_value = 0; h_value < h_limit; h_value++) {
            for (size_t k_depth = 0; k_depth <= 2; k_depth++) {
                unsigned k_limit = 1u << k_depth;
                for (unsigned k_value = 0; k_value < k_limit; k_value++) {
                    for (size_t r_depth = 0; r_depth <= 2; r_depth++) {
                        unsigned r_limit = 1u << r_depth;
                        for (unsigned r_value = 0; r_value < r_limit; r_value++) {
                            assert(build_cont_input(h_value, h_depth,
                                                    k_value, k_depth,
                                                    r_value, r_depth,
                                                    input, sizeof(input)));
                            assert_cont_algo_ct_case(input, decode_cont_holds(input));
                            checked++;
                        }
                    }
                }
            }
        }
    }

    printf("  cont_basic.algo CT runner: %zu bounded cases PASS\n", checked + 10);
}

int main(void) {
    printf("== test_cont ==\n");
    test_cont_basic_enum();
    test_cont_basic_algo();
    test_cont_algo_via_ct_runner();
    printf("ALL test_cont assertions passed (bounded Cont CT runner + decoder cross-check)\n");
    return 0;
}
