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

static size_t append_bit_chars(char *dst, size_t off, const char *bits, size_t len) {
    for (size_t i = 0; i < len; i++) {
        dst[off++] = bits[i];
    }
    dst[off] = '\0';
    return off;
}

static void bytes_to_bit_chars(const uint8_t *bytes, size_t len, char *out) {
    for (size_t i = 0; i < len; i++) {
        out[i] = bytes[i] ? '1' : '0';
    }
    out[len] = '\0';
}

static size_t encode_event_bits(const uint8_t *event,
                                size_t event_len,
                                char *out,
                                size_t out_cap) {
    uint8_t encoded[64];
    size_t len = gc_event_encode(event, event_len, encoded, sizeof(encoded));

    if (len == 0 || len + 1 > out_cap) return 0;
    bytes_to_bit_chars(encoded, len, out);
    return len;
}

static size_t encode_bhist_bits(const uint8_t *choices,
                                size_t depth,
                                char *out,
                                size_t out_cap) {
    BHist h;
    uint8_t encoded[64];
    size_t len;

    h.choices = (uint8_t *)choices;
    h.depth = depth;
    len = gc_bhist_encode(&h, encoded, sizeof(encoded));
    if (len == 0 || len + 1 > out_cap) return 0;
    bytes_to_bit_chars(encoded, len, out);
    return len;
}

static void make_bhist_choices(unsigned value,
                               size_t depth,
                               uint8_t *choices) {
    for (size_t i = 0; i < depth; i++) {
        size_t shift = depth - i - 1;
        choices[i] = (uint8_t)((value >> shift) & 1u);
    }
}

static size_t make_unary_event(size_t value, uint8_t *event, size_t cap) {
    if (value + 1 > cap) return 0;
    for (size_t i = 0; i < value; i++) event[i] = 0;
    event[value] = 1;
    return value + 1;
}

static void expected_positional_certificate(const char *input_bits,
                                            char *out,
                                            size_t out_cap) {
    size_t off = 0;
    size_t len = strlen(input_bits);

    assert(len <= 128);
    for (size_t i = 0; i < len; i++) {
        assert(input_bits[i] == '0' || input_bits[i] == '1');
        if (input_bits[i] == '1') {
            assert(off + 8 < out_cap);
            out[off++] = '1';
            for (int bit = 6; bit >= 0; bit--) {
                out[off++] = ((i >> (size_t)bit) & 1u) ? '1' : '0';
            }
        }
    }
    out[off] = '\0';
}

static int build_ingap_input(size_t domain_bound,
                             const size_t *probe_names,
                             size_t probe_count,
                             unsigned h_value,
                             size_t h_depth,
                             unsigned witness_value,
                             size_t witness_depth,
                             unsigned pkg_value,
                             size_t pkg_depth,
                             char *out,
                             size_t out_cap) {
    uint8_t event[8];
    uint8_t h_choices[4];
    uint8_t witness_choices[4];
    uint8_t pkg_choices[4];
    char encoded[64];
    size_t encoded_len;
    size_t event_len;
    size_t off = 0;

    if (out_cap == 0) return 0;

    event[0] = 0;
    encoded_len = encode_event_bits(event, 1, encoded, sizeof(encoded));
    if (encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
    off = append_bit_chars(out, off, encoded, encoded_len);

    event_len = make_unary_event(domain_bound, event, sizeof(event));
    encoded_len = encode_event_bits(event, event_len, encoded, sizeof(encoded));
    if (event_len == 0 || encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
    off = append_bit_chars(out, off, encoded, encoded_len);

    for (size_t i = 0; i < probe_count; i++) {
        event_len = make_unary_event(probe_names[i], event, sizeof(event));
        encoded_len = encode_event_bits(event, event_len, encoded, sizeof(encoded));
        if (event_len == 0 || encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
        off = append_bit_chars(out, off, encoded, encoded_len);
    }

    event[0] = 1;
    event[1] = 1;
    encoded_len = encode_event_bits(event, 2, encoded, sizeof(encoded));
    if (encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
    off = append_bit_chars(out, off, encoded, encoded_len);

    make_bhist_choices(h_value, h_depth, h_choices);
    encoded_len = encode_bhist_bits(h_choices, h_depth, encoded, sizeof(encoded));
    if (encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
    off = append_bit_chars(out, off, encoded, encoded_len);

    make_bhist_choices(witness_value, witness_depth, witness_choices);
    encoded_len = encode_bhist_bits(witness_choices, witness_depth, encoded, sizeof(encoded));
    if (encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
    off = append_bit_chars(out, off, encoded, encoded_len);

    make_bhist_choices(pkg_value, pkg_depth, pkg_choices);
    encoded_len = encode_bhist_bits(pkg_choices, pkg_depth, encoded, sizeof(encoded));
    if (encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
    append_bit_chars(out, off, encoded, encoded_len);
    return 1;
}

static int build_compgap_input(unsigned source_value,
                               size_t source_depth,
                               unsigned inter_value,
                               size_t inter_depth,
                               unsigned final_value,
                               size_t final_depth,
                               int first,
                               int second,
                               char *out,
                               size_t out_cap) {
    uint8_t event[2];
    uint8_t source_choices[4];
    uint8_t inter_choices[4];
    uint8_t final_choices[4];
    char encoded[64];
    size_t encoded_len;
    size_t off = 0;

    event[0] = 1;
    encoded_len = encode_event_bits(event, 1, encoded, sizeof(encoded));
    if (encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
    off = append_bit_chars(out, off, encoded, encoded_len);

    make_bhist_choices(source_value, source_depth, source_choices);
    encoded_len = encode_bhist_bits(source_choices, source_depth, encoded, sizeof(encoded));
    if (encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
    off = append_bit_chars(out, off, encoded, encoded_len);

    make_bhist_choices(inter_value, inter_depth, inter_choices);
    encoded_len = encode_bhist_bits(inter_choices, inter_depth, encoded, sizeof(encoded));
    if (encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
    off = append_bit_chars(out, off, encoded, encoded_len);

    make_bhist_choices(final_value, final_depth, final_choices);
    encoded_len = encode_bhist_bits(final_choices, final_depth, encoded, sizeof(encoded));
    if (encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
    off = append_bit_chars(out, off, encoded, encoded_len);

    event[0] = first ? 1 : 0;
    event[1] = second ? 1 : 0;
    encoded_len = encode_event_bits(event, 2, encoded, sizeof(encoded));
    if (encoded_len == 0 || off + encoded_len + 1 > out_cap) return 0;
    append_bit_chars(out, off, encoded, encoded_len);
    return 1;
}

static void free_bundle(ProbeBundleFixture *bundle) {
    free(bundle->names);
    bundle->names = NULL;
    bundle->len = 0;
}

static void free_bhist(BHist *h) {
    free(h->choices);
    h->choices = NULL;
    h->depth = 0;
}

static int bhist_equal(const BHist *a, const BHist *b) {
    return (a->depth == b->depth) &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
}

static int decode_unary_event_as_nat(const uint8_t *event, size_t event_len,
                                     size_t *value_out) {
    if (event_len == 0) return 0;
    for (size_t i = 0; i + 1 < event_len; i++) {
        if (event[i] != 0) return 0;
    }
    if (event[event_len - 1] != 1) return 0;
    *value_out = event_len - 1;
    return 1;
}

static int decode_tag_at(const uint8_t *input, size_t input_len,
                         size_t *off, uint8_t *tag_out) {
    GcDecResult event = gc_dec_event(input + *off, input_len - *off, 8192);
    if (event.status != GC_OK) {
        free(event.event);
        return 0;
    }
    int ok = (event.event_len == 1) && (event.event[0] == 0 || event.event[0] == 1);
    if (ok) {
        *tag_out = event.event[0];
        *off += event.bytes_consumed;
    }
    free(event.event);
    return ok;
}

static int decode_domain_at(const uint8_t *input, size_t input_len,
                            size_t *off, size_t *domain_out) {
    GcDecResult event = gc_dec_event(input + *off, input_len - *off, 8192);
    if (event.status != GC_OK) {
        free(event.event);
        return 0;
    }
    int ok = decode_unary_event_as_nat(event.event, event.event_len, domain_out);
    if (ok) *off += event.bytes_consumed;
    free(event.event);
    return ok;
}

static int decode_probe_bundle(const uint8_t *input, size_t input_len,
                               size_t *off, ProbeBundleFixture *bundle) {
    bundle->names = NULL;
    bundle->len = 0;
    size_t cap = 0;

    while (*off < input_len) {
        GcDecResult event = gc_dec_event(input + *off, input_len - *off, 8192);
        if (event.status != GC_OK) {
            free(event.event);
            free_bundle(bundle);
            return 0;
        }
        *off += event.bytes_consumed;

        if (event.event_len == 0) {
            free(event.event);
            return 1;
        }

        size_t name = 0;
        if (!decode_unary_event_as_nat(event.event, event.event_len, &name)) {
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

static int decode_relation_bits_at(const uint8_t *input, size_t input_len,
                                   size_t *off, int *first, int *second) {
    GcDecResult event = gc_dec_event(input + *off, input_len - *off, 8192);
    if (event.status != GC_OK) {
        free(event.event);
        return 0;
    }
    int ok = event.event_len == 2 &&
             (event.event[0] == 0 || event.event[0] == 1) &&
             (event.event[1] == 0 || event.event[1] == 1);
    if (ok) {
        *first = event.event[0] == 1;
        *second = event.event[1] == 1;
        *off += event.bytes_consumed;
    }
    free(event.event);
    return ok;
}

static int decode_ingap_holds_bytes(const uint8_t *bytes, size_t len, size_t off) {
    size_t domain_bound = 0;
    ProbeBundleFixture bundle;
    BHist h = {NULL, 0};
    BHist witness_sig = {NULL, 0};
    BHist pkg = {NULL, 0};
    BHist computed_sig = {NULL, 0};
    int ok = decode_domain_at(bytes, len, &off, &domain_bound);
    if (ok) ok = decode_probe_bundle(bytes, len, &off, &bundle);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &h);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &witness_sig);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &pkg);
    if (ok) ok = (off == len);
    if (ok) ok = compute_sigrel_result(&bundle, &h, &computed_sig);

    int holds = ok &&
                h.depth <= domain_bound &&
                bhist_equal(&computed_sig, &witness_sig) &&
                bhist_equal(&witness_sig, &pkg);

    free_bundle(&bundle);
    free_bhist(&h);
    free_bhist(&witness_sig);
    free_bhist(&pkg);
    free_bhist(&computed_sig);
    return holds;
}

static int decode_compgap_holds_bytes(const uint8_t *bytes, size_t len, size_t off) {
    BHist source = {NULL, 0};
    BHist inter = {NULL, 0};
    BHist final = {NULL, 0};
    int first = 0;
    int second = 0;
    int ok = decode_bhist_at(bytes, len, &off, &source);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &inter);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &final);
    if (ok) ok = decode_relation_bits_at(bytes, len, &off, &first, &second);
    if (ok) ok = (off == len);

    int holds = ok && first && second;

    free_bhist(&source);
    free_bhist(&inter);
    free_bhist(&final);
    return holds;
}

static int decode_gap_holds(const char *input_bits) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    size_t off = 0;
    uint8_t tag = 0;
    int ok = decode_tag_at(bytes, len, &off, &tag);
    int holds = 0;
    if (ok && tag == 0) {
        holds = decode_ingap_holds_bytes(bytes, len, off);
    } else if (ok && tag == 1) {
        holds = decode_compgap_holds_bytes(bytes, len, off);
    }

    free(bytes);
    return holds;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_gap_algo_ct_case_with_marker(const char *input_bits,
                                                int expected_holds,
                                                const char *expected_marker) {
    MrResult r;

    assert(decode_gap_holds(input_bits) == expected_holds);
    r = mr_run_ct_manifest("manifests/gap/gap_basic.algo.ct",
                           input_bits,
                           expected_marker,
                           strlen(input_bits));
    if (r != MR_PASS) {
        fprintf(stderr, "gap_basic.algo CT FAIL on input=%s: result=%d\n",
                input_bits, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_gap_algo_ct_case(const char *input_bits, int expected_holds) {
    char expected_marker[1024];

    expected_positional_certificate(input_bits,
                                    expected_marker,
                                    sizeof(expected_marker));
    assert_gap_algo_ct_case_with_marker(input_bits,
                                        expected_holds,
                                        expected_marker);
}

static void assert_gap_basic_cases(void) {
    assert(decode_gap_holds("011101111111111"));
    assert(decode_gap_holds("01101011101111101110111011"));
    assert(decode_gap_holds("01100101110110101111110101101011"));
    assert(!decode_gap_holds("0111011101111101110111011"));
    assert(!decode_gap_holds("011010111011111011111011"));
    assert(!decode_gap_holds("011010111011111011101111"));
    assert(!decode_gap_holds("0111011111111111011"));

    assert(decode_gap_holds("1011111111101011"));
    assert(decode_gap_holds("10111011101101011101011"));
    assert(decode_gap_holds("1011010111001110001011101011"));
    assert(!decode_gap_holds("1011101110110101101011"));
    assert(!decode_gap_holds("1011101110110101110011"));
    assert(!decode_gap_holds("10111111111011"));
    assert(!decode_gap_holds("001111"));
}

static void test_gap_basic_enum(void) {
    assert_gap_basic_cases();
    assert_manifest_smoke("manifests/gap/gap_basic.enum.ct", "011101111111111");
    printf("  gap_basic.enum: 14/14 cases PASS\n");
}

static void test_gap_basic_algo(void) {
    assert_gap_basic_cases();
    assert_gap_algo_ct_case_with_marker(
        "011101111111111",
        1,
        "10000001100000101000001110000101100001101000011110001000100010011000101010001011100011001000110110001110");
    printf("  gap_basic.algo: 14/14 decoder cases + CT smoke PASS\n");
}

static void test_gap_algo_via_ct_runner(void) {
    struct GapAlgoCase {
        const char *input;
        int holds;
        const char *marker;
    };
    const struct GapAlgoCase manifest_cases[] = {
        {"011101111111111", 1, "10000001100000101000001110000101100001101000011110001000100010011000101010001011100011001000110110001110"},
        {"01101011101111101110111011", 1, "10000001100000101000010010000110100001111000100010001010100010111000110010001101100011101001000010010001100100101001010010010101100101101001100010011001"},
        {"01100101110110101111110101101011", 1, "100000011000001010000101100001111000100010001001100010111000110010001110100100001001000110010010100100111001010010010101100101111001100110011010100111001001111010011111"},
        {"0111011101111101110111011", 0, "10000001100000101000001110000101100001101000011110001001100010101000101110001100100011011000111110010000100100011001001110010100100101011001011110011000"},
        {"011010111011111011111011", 0, "100000011000001010000100100001101000011110001000100010101000101110001100100011011000111010010000100100011001001010010011100101001001011010010111"},
        {"011010111011111011101111", 0, "100000011000001010000100100001101000011110001000100010101000101110001100100011011000111010010000100100011001001010010100100101011001011010010111"},
        {"0111011111111111011", 0, "10000001100000101000001110000101100001101000011110001000100010011000101010001011100011001000110110001110100011111001000110010010"},
        {"1011111111101011", 1, "10000000100000101000001110000100100001011000011010000111100010001000100110001010100011001000111010001111"},
        {"10111011101101011101011", 1, "10000000100000101000001110000100100001101000011110001000100010101000101110001101100011111001000010010001100100111001010110010110"},
        {"1011010111001110001011101011", 1, "1000000010000010100000111000010110000111100010001000100110001100100011011000111010010010100101001001010110010110100110001001101010011011"},
        {"1011101110110101101011", 0, "100000001000001010000011100001001000011010000111100010001000101010001011100011011000111110010000100100101001010010010101"},
        {"1011101110110101110011", 0, "100000001000001010000011100001001000011010000111100010001000101010001011100011011000111110010000100100011001010010010101"},
        {"10111111111011", 0, "100000001000001010000011100001001000010110000110100001111000100010001001100010101000110010001101"},
        {"001111", 0, "10000010100000111000010010000101"}
    };
    const size_t bundles[][2] = {
        {0, 0},
        {0, 1},
        {1, 0},
        {1, 2}
    };
    const size_t bundle_lens[] = {0, 1, 1, 2};
    char input[256];
    size_t checked = 0;

    for (size_t i = 0; i < sizeof(manifest_cases) / sizeof(manifest_cases[0]); i++) {
        assert_gap_algo_ct_case_with_marker(manifest_cases[i].input,
                                            manifest_cases[i].holds,
                                            manifest_cases[i].marker);
    }

    for (size_t bundle_idx = 0; bundle_idx < sizeof(bundle_lens) / sizeof(bundle_lens[0]); bundle_idx++) {
        size_t probe_count = bundle_lens[bundle_idx];
        for (size_t domain = 0; domain <= 2; domain++) {
            for (size_t h_depth = 0; h_depth <= 2; h_depth++) {
                unsigned h_limit = 1u << h_depth;
                for (unsigned h_value = 0; h_value < h_limit; h_value++) {
                    for (size_t witness_depth = 0; witness_depth <= 2; witness_depth++) {
                        unsigned witness_limit = 1u << witness_depth;
                        for (unsigned witness_value = 0; witness_value < witness_limit; witness_value++) {
                            for (size_t pkg_depth = 0; pkg_depth <= 2; pkg_depth++) {
                                unsigned pkg_limit = 1u << pkg_depth;
                                for (unsigned pkg_value = 0; pkg_value < pkg_limit; pkg_value++) {
                                    assert(build_ingap_input(domain,
                                                             bundles[bundle_idx],
                                                             probe_count,
                                                             h_value,
                                                             h_depth,
                                                             witness_value,
                                                             witness_depth,
                                                             pkg_value,
                                                             pkg_depth,
                                                             input,
                                                             sizeof(input)));
                                    assert_gap_algo_ct_case(input, decode_gap_holds(input));
                                    checked++;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    for (size_t source_depth = 0; source_depth <= 2; source_depth++) {
        unsigned source_limit = 1u << source_depth;
        for (unsigned source_value = 0; source_value < source_limit; source_value++) {
            for (size_t inter_depth = 0; inter_depth <= 2; inter_depth++) {
                unsigned inter_limit = 1u << inter_depth;
                for (unsigned inter_value = 0; inter_value < inter_limit; inter_value++) {
                    for (size_t final_depth = 0; final_depth <= 2; final_depth++) {
                        unsigned final_limit = 1u << final_depth;
                        for (unsigned final_value = 0; final_value < final_limit; final_value++) {
                            for (int first = 0; first <= 1; first++) {
                                for (int second = 0; second <= 1; second++) {
                                    assert(build_compgap_input(source_value,
                                                               source_depth,
                                                               inter_value,
                                                               inter_depth,
                                                               final_value,
                                                               final_depth,
                                                               first,
                                                               second,
                                                               input,
                                                               sizeof(input)));
                                    assert_gap_algo_ct_case(input, decode_gap_holds(input));
                                    checked++;
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    printf("  gap_basic.algo CT runner: %zu bounded cases PASS\n",
           checked + 14);
}

int main(void) {
    printf("== test_gap ==\n");
    test_gap_basic_enum();
    test_gap_basic_algo();
    test_gap_algo_via_ct_runner();
    printf("ALL test_gap assertions passed (bounded Gap CT runner + decoder cross-check)\n");
    return 0;
}
