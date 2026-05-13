#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct {
    size_t *names;
    size_t len;
} ProbeBundleFixture;

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

static void free_bundle(ProbeBundleFixture *bundle) {
    free(bundle->names);
    bundle->names = NULL;
    bundle->len = 0;
}

static int bhist_equal(const BHist *a, const BHist *b) {
    return (a->depth == b->depth) &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
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

static size_t encode_probe_name_bits(size_t probe_name,
                                     char *out,
                                     size_t out_cap) {
    size_t off = 0;

    if (probe_name + 3 > out_cap) return 0;
    for (size_t i = 0; i < probe_name; i++) {
        out[off++] = '0';
    }
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

static void make_bundle_names(unsigned value,
                              size_t len,
                              size_t *names) {
    for (size_t i = 0; i < len; i++) {
        size_t shift = len - i - 1;
        names[i] = (size_t)((value >> (2 * shift)) & 3u);
    }
}

static int build_sigrel_input(const size_t *names,
                              size_t bundle_len,
                              unsigned h_value,
                              size_t h_depth,
                              unsigned r_value,
                              size_t r_depth,
                              char *out,
                              size_t out_cap) {
    uint8_t h_choices[4];
    uint8_t r_choices[4];
    char h_bits[16];
    char r_bits[16];
    size_t h_len;
    size_t r_len;
    size_t off = 0;

    for (size_t i = 0; i < bundle_len; i++) {
        char probe_bits[16];
        size_t probe_len = encode_probe_name_bits(names[i],
                                                  probe_bits,
                                                  sizeof(probe_bits));
        if (probe_len == 0 || off + probe_len >= out_cap) return 0;
        off = append_bit_chars(out, off, probe_bits, probe_len);
    }

    if (off + 2 >= out_cap) return 0;
    out[off++] = '1';
    out[off++] = '1';
    out[off] = '\0';

    make_bhist_choices(h_value, h_depth, h_choices);
    make_bhist_choices(r_value, r_depth, r_choices);

    h_len = encode_bhist_bits(h_choices, h_depth, h_bits, sizeof(h_bits));
    r_len = encode_bhist_bits(r_choices, r_depth, r_bits, sizeof(r_bits));
    if (h_len == 0 || r_len == 0) return 0;
    if (off + h_len + r_len + 1 > out_cap) return 0;

    off = append_bit_chars(out, off, h_bits, h_len);
    append_bit_chars(out, off, r_bits, r_len);
    return 1;
}

static int build_samesig_input(const size_t *names,
                               size_t bundle_len,
                               unsigned h_value,
                               size_t h_depth,
                               unsigned k_value,
                               size_t k_depth,
                               char *out,
                               size_t out_cap) {
    return build_sigrel_input(names,
                              bundle_len,
                              h_value,
                              h_depth,
                              k_value,
                              k_depth,
                              out,
                              out_cap);
}

static char *sig_algo_certificate(const char *input_bits) {
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

static int decode_probe_bundle(const uint8_t *input, size_t input_len,
                               ProbeBundleFixture *bundle, size_t *off_out) {
    bundle->names = NULL;
    bundle->len = 0;
    size_t cap = 0;
    size_t off = 0;

    while (off < input_len) {
        GcDecResult event = gc_dec_event(input + off, input_len - off, 8192);
        if (event.status != GC_OK) {
            free(event.event);
            free_bundle(bundle);
            return 0;
        }
        off += event.bytes_consumed;

        if (event.event_len == 0) {
            free(event.event);
            *off_out = off;
            return 1;
        }

        size_t name = 0;
        if (!decode_probe_name_event(event.event, event.event_len, &name)) {
            free(event.event);
            free_bundle(bundle);
            return 0;
        }
        free(event.event);

        if (bundle->len == cap) {
            size_t next_cap = cap == 0 ? 4 : cap * 2;
            size_t *next = (size_t *)realloc(bundle->names, next_cap * sizeof(size_t));
            if (next == NULL) {
                free_bundle(bundle);
                return 0;
            }
            bundle->names = next;
            cap = next_cap;
        }
        bundle->names[bundle->len++] = name;
    }

    free_bundle(bundle);
    return 0;
}

static int decode_bhist_at(const uint8_t *input, size_t input_len,
                           size_t *off, BHist *out) {
    GcBhistDecResult decoded = gc_bhist_decode(input + *off, input_len - *off, 8192);
    if (decoded.status != GC_OK) {
        free(decoded.bhist.choices);
        return 0;
    }
    *off += decoded.bytes_consumed;
    *out = decoded.bhist;
    return 1;
}

static uint8_t fixture_ask_mark(size_t probe_name, const BHist *h) {
    return (uint8_t)((probe_name + h->depth) & 1u);
}

static int compute_sigrel_result(const ProbeBundleFixture *bundle,
                                 const BHist *source,
                                 BHist *out) {
    uint8_t *choices = NULL;
    if (bundle->len > 0) {
        choices = (uint8_t *)malloc(bundle->len);
        if (choices == NULL) return 0;
    }
    for (size_t i = 0; i < bundle->len; i++) {
        choices[i] = fixture_ask_mark(bundle->names[i], source);
    }
    out->choices = choices;
    out->depth = bundle->len;
    return 1;
}

static int decode_sigrel_holds(const char *input_bits) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    ProbeBundleFixture bundle;
    size_t off = 0;
    int ok = decode_probe_bundle(bytes, len, &bundle, &off);

    BHist source = {NULL, 0};
    BHist encoded_result = {NULL, 0};
    BHist computed = {NULL, 0};
    if (ok) ok = decode_bhist_at(bytes, len, &off, &source);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &encoded_result);
    if (ok) ok = (off == len);
    if (ok) ok = compute_sigrel_result(&bundle, &source, &computed);

    int holds = ok && bhist_equal(&computed, &encoded_result);
    free(bytes);
    free_bundle(&bundle);
    free(source.choices);
    free(encoded_result.choices);
    free(computed.choices);
    return holds;
}

static int decode_sameSig_holds_bytes(const uint8_t *bytes, size_t len,
                                      size_t *off, const ProbeBundleFixture *bundle,
                                      BHist *h_out, BHist *k_out) {
    BHist sig_h = {NULL, 0};
    BHist sig_k = {NULL, 0};
    int ok = decode_bhist_at(bytes, len, off, h_out);
    if (ok) ok = decode_bhist_at(bytes, len, off, k_out);
    if (ok) ok = compute_sigrel_result(bundle, h_out, &sig_h);
    if (ok) ok = compute_sigrel_result(bundle, k_out, &sig_k);
    int holds = ok && bhist_equal(&sig_h, &sig_k);
    free(sig_h.choices);
    free(sig_k.choices);
    return holds;
}

static int decode_sameSig_holds(const char *input_bits) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    ProbeBundleFixture bundle;
    size_t off = 0;
    int ok = decode_probe_bundle(bytes, len, &bundle, &off);
    BHist h = {NULL, 0};
    BHist k = {NULL, 0};
    int holds = 0;
    if (ok) holds = decode_sameSig_holds_bytes(bytes, len, &off, &bundle, &h, &k);
    if (ok) ok = (off == len);
    holds = holds && ok;

    free(bytes);
    free_bundle(&bundle);
    free(h.choices);
    free(k.choices);
    return holds;
}

static int decode_sameSig_symm_check(const char *input_bits) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    ProbeBundleFixture bundle;
    size_t off = 0;
    int ok = decode_probe_bundle(bytes, len, &bundle, &off);
    BHist h = {NULL, 0};
    BHist k = {NULL, 0};
    BHist sig_h = {NULL, 0};
    BHist sig_k = {NULL, 0};

    if (ok) ok = decode_bhist_at(bytes, len, &off, &h);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &k);
    if (ok) ok = (off == len);
    if (ok) ok = compute_sigrel_result(&bundle, &h, &sig_h);
    if (ok) ok = compute_sigrel_result(&bundle, &k, &sig_k);

    int forward = ok && bhist_equal(&sig_h, &sig_k);
    int backward = ok && bhist_equal(&sig_k, &sig_h);
    int theorem_ok = ok && (!forward || backward);

    free(bytes);
    free_bundle(&bundle);
    free(h.choices);
    free(k.choices);
    free(sig_h.choices);
    free(sig_k.choices);
    return theorem_ok;
}

static int decode_sameSig_trans_check(const char *input_bits) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    ProbeBundleFixture bundle;
    size_t off = 0;
    int ok = decode_probe_bundle(bytes, len, &bundle, &off);
    BHist h = {NULL, 0};
    BHist k = {NULL, 0};
    BHist l = {NULL, 0};
    BHist sig_h = {NULL, 0};
    BHist sig_k = {NULL, 0};
    BHist sig_l = {NULL, 0};

    if (ok) ok = decode_bhist_at(bytes, len, &off, &h);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &k);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &l);
    if (ok) ok = (off == len);
    if (ok) ok = compute_sigrel_result(&bundle, &h, &sig_h);
    if (ok) ok = compute_sigrel_result(&bundle, &k, &sig_k);
    if (ok) ok = compute_sigrel_result(&bundle, &l, &sig_l);

    int hk = ok && bhist_equal(&sig_h, &sig_k);
    int kl = ok && bhist_equal(&sig_k, &sig_l);
    int hl = ok && bhist_equal(&sig_h, &sig_l);
    int theorem_ok = ok && (!(hk && kl) || hl);

    free(bytes);
    free_bundle(&bundle);
    free(h.choices);
    free(k.choices);
    free(l.choices);
    free(sig_h.choices);
    free(sig_k.choices);
    free(sig_l.choices);
    return theorem_ok;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_sigrel_algo_ct_case_with_marker(const char *input_bits,
                                                   int expected_holds,
                                                   const char *expected_marker) {
    MrResult r;

    assert(decode_sigrel_holds(input_bits) == expected_holds);
    r = mr_run_ct_manifest("manifests/sig/sigrel_basic.algo.ct",
                           input_bits,
                           expected_marker,
                           strlen(input_bits));
    if (r != MR_PASS) {
        fprintf(stderr, "sigrel_basic.algo CT FAIL on input=%s: result=%d\n",
                input_bits, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_sigrel_algo_ct_case(const char *input_bits, int expected_holds) {
    char *expected = sig_algo_certificate(input_bits);

    assert_sigrel_algo_ct_case_with_marker(input_bits, expected_holds, expected);
    free(expected);
}

static void assert_samesig_algo_holds_ct_case_with_marker(const char *input_bits,
                                                          int expected_holds,
                                                          const char *expected_marker) {
    MrResult r;

    assert(decode_sameSig_holds(input_bits) == expected_holds);
    r = mr_run_ct_manifest("manifests/sig/samesig_equiv.algo.ct",
                           input_bits,
                           expected_marker,
                           strlen(input_bits));
    if (r != MR_PASS) {
        fprintf(stderr, "samesig_equiv.algo CT FAIL on input=%s: result=%d\n",
                input_bits, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_samesig_algo_holds_ct_case(const char *input_bits,
                                              int expected_holds) {
    char *expected = sig_algo_certificate(input_bits);

    assert_samesig_algo_holds_ct_case_with_marker(input_bits,
                                                  expected_holds,
                                                  expected);
    free(expected);
}

static void assert_samesig_algo_symm_ct_case_with_marker(const char *input_bits,
                                                         const char *expected_marker) {
    MrResult r;

    assert(decode_sameSig_symm_check(input_bits));
    r = mr_run_ct_manifest("manifests/sig/samesig_equiv.algo.ct",
                           input_bits,
                           expected_marker,
                           strlen(input_bits));
    if (r != MR_PASS) {
        fprintf(stderr, "samesig_equiv.algo symm CT FAIL on input=%s: result=%d\n",
                input_bits, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_samesig_algo_trans_ct_case_with_marker(const char *input_bits,
                                                          const char *expected_marker) {
    MrResult r;

    assert(decode_sameSig_trans_check(input_bits));
    r = mr_run_ct_manifest("manifests/sig/samesig_equiv.algo.ct",
                           input_bits,
                           expected_marker,
                           strlen(input_bits));
    if (r != MR_PASS) {
        fprintf(stderr, "samesig_equiv.algo trans CT FAIL on input=%s: result=%d\n",
                input_bits, (int)r);
    }
    assert(r == MR_PASS);
}

static void test_sigrel_basic_enum(void) {
    assert(decode_sigrel_holds("111111"));
    assert(decode_sigrel_holds("11101111"));
    assert(!decode_sigrel_holds("1111011"));
    assert(decode_sigrel_holds("10111111011"));
    assert(decode_sigrel_holds("1011110111011"));
    assert(!decode_sigrel_holds("101111111011"));
    assert(decode_sigrel_holds("0101111111011"));
    assert(decode_sigrel_holds("101101011111101011"));
    assert(!decode_sigrel_holds("10110101111110011"));
    assert_manifest_smoke("manifests/sig/sigrel_basic.enum.ct", "111111");
    printf("  sigrel_basic.enum: 9/9 cases PASS\n");
}

static void test_sigrel_basic_algo(void) {
    assert(decode_sigrel_holds("111111"));
    assert(decode_sigrel_holds("11101111"));
    assert(!decode_sigrel_holds("1111011"));
    assert(decode_sigrel_holds("10111111011"));
    assert(decode_sigrel_holds("1011110111011"));
    assert(!decode_sigrel_holds("101111111011"));
    assert(decode_sigrel_holds("0101111111011"));
    assert(decode_sigrel_holds("101101011111101011"));
    assert(!decode_sigrel_holds("10110101111110011"));
    assert_sigrel_algo_ct_case_with_marker(
        "111111", 1, "100000010000011000010100001110001001000101");
    printf("  sigrel_basic.algo: 9/9 decoder cases + CT smoke PASS\n");
}

static void test_sigrel_algo_via_ct_runner(void) {
    struct SigRelAlgoCase {
        const char *input;
        int holds;
        const char *marker;
    };
    const struct SigRelAlgoCase manifest_cases[] = {
        {"111111", 1, "100000010000011000010100001110001001000101"},
        {"11101111", 1, "1000000100000110000101000100100010110001101000111"},
        {"1111011", 0, "100000010000011000010100001110001011000110"},
        {"10111111011", 1, "100000010000101000011100010010001011000110100011110010011001010"},
        {"1011110111011", 1, "1000000100001010000111000100100010110001111001000100100110010111001100"},
        {"101111111011", 0, "1000000100001010000111000100100010110001101000111100100010010101001011"},
        {"0101111111011", 1, "1000001100001110001001000101100011010001111001000100100110010111001100"},
        {"101101011111101011", 1, "1000000100001010000111000101100011110010001001001100101010010111001100100111010100001010001"},
        {"10110101111110011", 0, "100000010000101000011100010110001111001000100100110010101001011100110010011111010000"}
    };
    const char *malformed_cases[] = {
        "",
        "1",
        "0",
        "101",
        "111110",
        "1011110110110"
    };
    char input[96];
    size_t names[2];
    size_t checked = 0;

    for (size_t i = 0; i < sizeof(manifest_cases) / sizeof(manifest_cases[0]); i++) {
        assert_sigrel_algo_ct_case_with_marker(manifest_cases[i].input,
                                               manifest_cases[i].holds,
                                               manifest_cases[i].marker);
    }

    for (size_t bundle_len = 0; bundle_len <= 2; bundle_len++) {
        unsigned bundle_limit = 1u << (2 * bundle_len);
        for (unsigned bundle_value = 0; bundle_value < bundle_limit; bundle_value++) {
            make_bundle_names(bundle_value, bundle_len, names);
            for (size_t h_depth = 0; h_depth <= 2; h_depth++) {
                unsigned h_limit = 1u << h_depth;
                for (unsigned h_value = 0; h_value < h_limit; h_value++) {
                    for (size_t r_depth = 0; r_depth <= 2; r_depth++) {
                        unsigned r_limit = 1u << r_depth;
                        for (unsigned r_value = 0; r_value < r_limit; r_value++) {
                            assert(build_sigrel_input(names, bundle_len,
                                                      h_value, h_depth,
                                                      r_value, r_depth,
                                                      input, sizeof(input)));
                            assert_sigrel_algo_ct_case(input, decode_sigrel_holds(input));
                            checked++;
                        }
                    }
                }
            }
        }
    }

    for (size_t i = 0; i < sizeof(malformed_cases) / sizeof(malformed_cases[0]); i++) {
        assert_sigrel_algo_ct_case(malformed_cases[i], 0);
        checked++;
    }

    printf("  sigrel_basic.algo CT runner: %zu bounded cases PASS\n",
           checked + sizeof(manifest_cases) / sizeof(manifest_cases[0]));
}

static void test_samesig_equiv_enum(void) {
    assert(decode_sameSig_holds("111111"));
    assert(decode_sameSig_holds("101111011011"));
    assert(decode_sameSig_holds("101101011110101101011"));
    assert(decode_sameSig_symm_check("1111011"));
    assert(decode_sameSig_symm_check("1011110111011"));
    assert(decode_sameSig_symm_check("101111111011"));
    assert(decode_sameSig_symm_check("101111101111"));
    assert(decode_sameSig_trans_check("101101011111101011101011"));
    assert(decode_sameSig_trans_check("101101011111101101011"));
    assert_manifest_smoke("manifests/sig/samesig_equiv.enum.ct", "111111");
    printf("  samesig_equiv.enum: 9/9 cases PASS\n");
}

static void test_samesig_equiv_algo(void) {
    assert(decode_sameSig_holds("111111"));
    assert(decode_sameSig_holds("101111011011"));
    assert(decode_sameSig_holds("101101011110101101011"));
    assert(decode_sameSig_symm_check("1111011"));
    assert(decode_sameSig_symm_check("1011110111011"));
    assert(decode_sameSig_symm_check("101111111011"));
    assert(decode_sameSig_symm_check("101111101111"));
    assert(decode_sameSig_trans_check("101101011111101011101011"));
    assert(decode_sameSig_trans_check("101101011111101101011"));
    assert_samesig_algo_holds_ct_case_with_marker(
        "111111", 1, "100000010000011000010100001110001001000101");
    printf("  samesig_equiv.algo: 9/9 decoder cases + CT smoke PASS\n");
}

static void test_samesig_algo_via_ct_runner(void) {
    struct SameSigHoldsCase {
        const char *input;
        int holds;
        const char *marker;
    };
    const struct SameSigHoldsCase holds_cases[] = {
        {"111111", 1, "100000010000011000010100001110001001000101"},
        {"101111011011", 1, "100000010000101000011100010010001011000111100100010010101001011"},
        {"101101011110101101011", 1, "10000001000010100001110001011000111100100010010011001010100110010011101001111101000110100111010100"}
    };
    struct SameSigTheoremCase {
        const char *input;
        const char *marker;
    };
    const struct SameSigTheoremCase symm_cases[] = {
        {"1111011", "100000010000011000010100001110001011000110"},
        {"1011110111011", "1000000100001010000111000100100010110001111001000100100110010111001100"},
        {"101111111011", "1000000100001010000111000100100010110001101000111100100010010101001011"},
        {"101111101111", "1000000100001010000111000100100010110001101001000100100110010101001011"}
    };
    const struct SameSigTheoremCase trans_cases[] = {
        {"101101011111101011101011", "10000001000010100001110001011000111100100010010011001010100101110011001001110101000010100011010010101010010101101010111"},
        {"101101011111101101011", "100000010000101000011100010110001111001000100100110010101001011100110010011101001111101000110100111010100"}
    };
    const char *malformed_cases[] = {
        "",
        "1",
        "0",
        "101",
        "111110",
        "1011110110110"
    };
    char input[96];
    size_t names[2];
    size_t checked = 0;

    for (size_t i = 0; i < sizeof(holds_cases) / sizeof(holds_cases[0]); i++) {
        assert_samesig_algo_holds_ct_case_with_marker(holds_cases[i].input,
                                                      holds_cases[i].holds,
                                                      holds_cases[i].marker);
    }
    for (size_t i = 0; i < sizeof(symm_cases) / sizeof(symm_cases[0]); i++) {
        assert_samesig_algo_symm_ct_case_with_marker(symm_cases[i].input,
                                                     symm_cases[i].marker);
    }
    for (size_t i = 0; i < sizeof(trans_cases) / sizeof(trans_cases[0]); i++) {
        assert_samesig_algo_trans_ct_case_with_marker(trans_cases[i].input,
                                                      trans_cases[i].marker);
    }

    for (size_t bundle_len = 0; bundle_len <= 2; bundle_len++) {
        unsigned bundle_limit = 1u << (2 * bundle_len);
        for (unsigned bundle_value = 0; bundle_value < bundle_limit; bundle_value++) {
            make_bundle_names(bundle_value, bundle_len, names);
            for (size_t h_depth = 0; h_depth <= 2; h_depth++) {
                unsigned h_limit = 1u << h_depth;
                for (unsigned h_value = 0; h_value < h_limit; h_value++) {
                    for (size_t k_depth = 0; k_depth <= 2; k_depth++) {
                        unsigned k_limit = 1u << k_depth;
                        for (unsigned k_value = 0; k_value < k_limit; k_value++) {
                            assert(build_samesig_input(names, bundle_len,
                                                       h_value, h_depth,
                                                       k_value, k_depth,
                                                       input, sizeof(input)));
                            assert_samesig_algo_holds_ct_case(input,
                                                              decode_sameSig_holds(input));
                            checked++;
                        }
                    }
                }
            }
        }
    }

    for (size_t i = 0; i < sizeof(malformed_cases) / sizeof(malformed_cases[0]); i++) {
        assert_samesig_algo_holds_ct_case(malformed_cases[i], 0);
        checked++;
    }

    printf("  samesig_equiv.algo CT runner: %zu bounded cases PASS\n",
           checked +
           sizeof(holds_cases) / sizeof(holds_cases[0]) +
           sizeof(symm_cases) / sizeof(symm_cases[0]) +
           sizeof(trans_cases) / sizeof(trans_cases[0]));
}

static void pipeline_smoke_test_sig_manifests(void) {
    struct { const char *path; const char *input; } enum_cases[] = {
        {"manifests/sig/sigrel_basic.enum.ct",   "111111"},
        {"manifests/sig/samesig_equiv.enum.ct",  "111111"}
    };
    size_t n = sizeof(enum_cases) / sizeof(enum_cases[0]);
    for (size_t i = 0; i < n; i++) {
        assert_manifest_smoke(enum_cases[i].path, enum_cases[i].input);
    }
    assert_sigrel_algo_ct_case("111111", 1);
    assert_samesig_algo_holds_ct_case("111111", 1);
    printf("  pipeline_smoke (2 enum halt-empty + 2 algo certificate sig manifests): PASS\n");
}

int main(void) {
    printf("== test_sig ==\n");
    test_sigrel_basic_enum();
    test_sigrel_basic_algo();
    test_sigrel_algo_via_ct_runner();
    test_samesig_equiv_enum();
    test_samesig_equiv_algo();
    test_samesig_algo_via_ct_runner();
    pipeline_smoke_test_sig_manifests();
    printf("ALL test_sig assertions passed (bounded Sig CT runners + decoder cross-check)\n");
    return 0;
}
