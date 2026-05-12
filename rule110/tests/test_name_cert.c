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

static int decode_nat_at(const uint8_t *input, size_t input_len,
                         size_t *off, size_t *value_out) {
    GcDecResult event = gc_dec_event(input + *off, input_len - *off, 8192);
    if (event.status != GC_OK) {
        free_event_result(&event);
        return 0;
    }
    int ok = decode_unary_event_as_nat(event.event, event.event_len, value_out);
    if (ok) *off += event.bytes_consumed;
    free_event_result(&event);
    return ok;
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

static int decode_bits_event_at(const uint8_t *input, size_t input_len,
                                size_t *off, uint8_t *out, size_t expected_len) {
    GcDecResult event = gc_dec_event(input + *off, input_len - *off, 8192);
    if (event.status != GC_OK) {
        free_event_result(&event);
        return 0;
    }
    int ok = event.event_len == expected_len;
    for (size_t i = 0; ok && i < expected_len; i++) {
        ok = event.event[i] == 0 || event.event[i] == 1;
        if (ok) out[i] = event.event[i];
    }
    if (ok) *off += event.bytes_consumed;
    free_event_result(&event);
    return ok;
}

static int carrier_holds(size_t bound, const BHist *h) {
    return h->depth <= bound;
}

static int equiv_holds(const BHist *a, const BHist *b) {
    return a->depth == b->depth;
}

static int bit_matches(uint8_t bit, int truth) {
    return (bit == 1) == (truth != 0);
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

static int append_unary_nat_event_chars(size_t value,
                                        char *out,
                                        size_t out_cap,
                                        size_t *out_pos) {
    uint8_t event[16];

    if (value + 1 > sizeof(event)) return 0;
    for (size_t i = 0; i < value; i++) event[i] = 0;
    event[value] = 1;
    return append_encoded_event_chars(event, value + 1, out, out_cap, out_pos);
}

static void make_bhist_choices(unsigned value,
                               size_t depth,
                               uint8_t *choices) {
    for (size_t i = 0; i < depth; i++) {
        size_t shift = depth - i - 1;
        choices[i] = (uint8_t)((value >> shift) & 1u);
    }
}

static int append_bhist_chars(unsigned value,
                              size_t depth,
                              char *out,
                              size_t out_cap,
                              size_t *out_pos) {
    uint8_t choices[8];

    if (depth > sizeof(choices)) return 0;
    make_bhist_choices(value, depth, choices);
    return append_encoded_event_chars(choices, depth, out, out_cap, out_pos);
}

static int append_bit_event_chars(const uint8_t *bits,
                                  size_t bit_len,
                                  char *out,
                                  size_t out_cap,
                                  size_t *out_pos) {
    return append_encoded_event_chars(bits, bit_len, out, out_cap, out_pos);
}

static int build_core_or_semantic_input(size_t tag,
                                        size_t bound,
                                        unsigned h_value,
                                        size_t h_depth,
                                        unsigned k_value,
                                        size_t k_depth,
                                        unsigned r_value,
                                        size_t r_depth,
                                        const uint8_t rel[3],
                                        char *out,
                                        size_t out_cap) {
    size_t out_pos = 0;

    out[0] = '\0';
    return append_unary_nat_event_chars(tag, out, out_cap, &out_pos) &&
           append_unary_nat_event_chars(bound, out, out_cap, &out_pos) &&
           append_bhist_chars(h_value, h_depth, out, out_cap, &out_pos) &&
           append_bhist_chars(k_value, k_depth, out, out_cap, &out_pos) &&
           append_bhist_chars(r_value, r_depth, out, out_cap, &out_pos) &&
           append_bit_event_chars(rel, 3, out, out_cap, &out_pos);
}

static int build_seal_input(size_t thread,
                            size_t bound,
                            char *out,
                            size_t out_cap) {
    size_t out_pos = 0;

    out[0] = '\0';
    return append_unary_nat_event_chars(2, out, out_cap, &out_pos) &&
           append_unary_nat_event_chars(thread, out, out_cap, &out_pos) &&
           append_unary_nat_event_chars(bound, out, out_cap, &out_pos);
}

static int build_stable_or_composition_input(size_t tag,
                                             unsigned source_value,
                                             size_t source_depth,
                                             unsigned target_value,
                                             size_t target_depth,
                                             const uint8_t *rel,
                                             size_t rel_len,
                                             char *out,
                                             size_t out_cap) {
    size_t out_pos = 0;

    out[0] = '\0';
    return append_unary_nat_event_chars(tag, out, out_cap, &out_pos) &&
           append_bhist_chars(source_value, source_depth, out, out_cap, &out_pos) &&
           append_bhist_chars(target_value, target_depth, out, out_cap, &out_pos) &&
           append_bit_event_chars(rel, rel_len, out, out_cap, &out_pos);
}

static int build_mode_input(size_t left,
                            size_t right,
                            char *out,
                            size_t out_cap) {
    size_t out_pos = 0;

    out[0] = '\0';
    return append_unary_nat_event_chars(5, out, out_cap, &out_pos) &&
           append_unary_nat_event_chars(left, out, out_cap, &out_pos) &&
           append_unary_nat_event_chars(right, out, out_cap, &out_pos);
}

static int check_core(const uint8_t *bytes, size_t len, size_t off) {
    size_t bound = 0;
    BHist h = {NULL, 0};
    BHist k = {NULL, 0};
    BHist r = {NULL, 0};
    uint8_t rel[3] = {0, 0, 0};

    int ok = decode_nat_at(bytes, len, &off, &bound);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &h);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &k);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &r);
    if (ok) ok = decode_bits_event_at(bytes, len, &off, rel, 3);
    if (ok) ok = off == len;

    int hk = equiv_holds(&h, &k);
    int kr = equiv_holds(&k, &r);
    int source = carrier_holds(bound, &h);
    int obligations = ok &&
        bit_matches(rel[0], hk) &&
        bit_matches(rel[1], kr) &&
        bit_matches(rel[2], source) &&
        (!source || equiv_holds(&h, &h)) &&
        (!hk || equiv_holds(&k, &h)) &&
        (!(hk && kr) || equiv_holds(&h, &r)) &&
        (!(hk && source) || carrier_holds(bound, &k));

    free_bhist(&h);
    free_bhist(&k);
    free_bhist(&r);
    return obligations;
}

static int check_semantic(const uint8_t *bytes, size_t len, size_t off) {
    size_t bound = 0;
    BHist h = {NULL, 0};
    BHist k = {NULL, 0};
    BHist r = {NULL, 0};
    uint8_t rel[3] = {0, 0, 0};

    int ok = decode_nat_at(bytes, len, &off, &bound);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &h);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &k);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &r);
    if (ok) ok = decode_bits_event_at(bytes, len, &off, rel, 3);
    if (ok) ok = off == len;

    int hk = equiv_holds(&h, &k);
    int kr = equiv_holds(&k, &r);
    int source = carrier_holds(bound, &h);
    int obligations = ok &&
        bit_matches(rel[0], hk) &&
        bit_matches(rel[1], kr) &&
        bit_matches(rel[2], source) &&
        (!source || (carrier_holds(bound, &h) && carrier_holds(bound, &h))) &&
        (!(hk && source) || carrier_holds(bound, &k)) &&
        (!(hk && kr && source) || carrier_holds(bound, &r));

    free_bhist(&h);
    free_bhist(&k);
    free_bhist(&r);
    return obligations;
}

static int check_seal(const uint8_t *bytes, size_t len, size_t off) {
    size_t thread = 0;
    size_t bound = 0;
    BHist empty = {NULL, 0};
    int ok = decode_nat_at(bytes, len, &off, &thread);
    if (ok) ok = decode_nat_at(bytes, len, &off, &bound);
    if (ok) ok = off == len;
    (void)thread;
    return ok && carrier_holds(bound, &empty);
}

static int check_stable(const uint8_t *bytes, size_t len, size_t off) {
    BHist source = {NULL, 0};
    BHist target = {NULL, 0};
    uint8_t rel[2] = {0, 0};

    int ok = decode_bhist_at(bytes, len, &off, &source);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &target);
    if (ok) ok = decode_bits_event_at(bytes, len, &off, rel, 2);
    if (ok) ok = off == len;

    int same = equiv_holds(&source, &target);
    int obligations = ok &&
        bit_matches(rel[0], same) &&
        rel[1] == 1 &&
        (!same || equiv_holds(&source, &target));

    free_bhist(&source);
    free_bhist(&target);
    return obligations;
}

static int check_composition(const uint8_t *bytes, size_t len, size_t off) {
    BHist source = {NULL, 0};
    BHist target = {NULL, 0};
    uint8_t rel[3] = {0, 0, 0};

    int ok = decode_bhist_at(bytes, len, &off, &source);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &target);
    if (ok) ok = decode_bits_event_at(bytes, len, &off, rel, 3);
    if (ok) ok = off == len;

    int same = equiv_holds(&source, &target);
    int obligations = ok &&
        bit_matches(rel[0], same) &&
        rel[1] == 1 &&
        rel[2] == 1 &&
        (!same || equiv_holds(&source, &target));

    free_bhist(&source);
    free_bhist(&target);
    return obligations;
}

static int check_mode(const uint8_t *bytes, size_t len, size_t off) {
    size_t left = 0;
    size_t right = 0;
    int ok = decode_nat_at(bytes, len, &off, &left);
    if (ok) ok = decode_nat_at(bytes, len, &off, &right);
    if (ok) ok = off == len;
    return ok && left < 5 && right < 5 && left != right;
}

static int decode_name_cert_holds(const char *input_bits) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    size_t off = 0;
    size_t tag = 0;
    int ok = decode_nat_at(bytes, len, &off, &tag);
    int holds = 0;
    if (ok && tag == 0) {
        holds = check_core(bytes, len, off);
    } else if (ok && tag == 1) {
        holds = check_semantic(bytes, len, off);
    } else if (ok && tag == 2) {
        holds = check_seal(bytes, len, off);
    } else if (ok && tag == 3) {
        holds = check_stable(bytes, len, off);
    } else if (ok && tag == 4) {
        holds = check_composition(bytes, len, off);
    } else if (ok && tag == 5) {
        holds = check_mode(bytes, len, off);
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

static void assert_name_cert_algo_ct_case(const char *input_bits,
                                          int expected_holds) {
    char expected_marker[1024];
    MrResult r;

    assert(decode_name_cert_holds(input_bits) == expected_holds);
    expected_positional_certificate(input_bits,
                                    expected_marker,
                                    sizeof(expected_marker));
    r = mr_run_ct_manifest("manifests/name_cert/name_cert_basic.algo.ct",
                           input_bits,
                           expected_marker,
                           strlen(input_bits));
    if (r != MR_PASS) {
        fprintf(stderr, "name_cert_basic.algo CT FAIL on input=%s: result=%d\n",
                input_bits, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_name_cert_cases(void) {
    assert(decode_name_cert_holds("1011101111111110101011"));
    assert(decode_name_cert_holds("101101011011101101110101011"));
    assert(decode_name_cert_holds("10111011011101111100011"));
    assert(!decode_name_cert_holds("10111011111011101110101011"));
    assert(!decode_name_cert_holds("10111011011101101110101011"));

    assert(decode_name_cert_holds("01011101111111110101011"));
    assert(decode_name_cert_holds("0101100101101011101011001110101011"));
    assert(decode_name_cert_holds("01011101101110110111010011"));
    assert(!decode_name_cert_holds("01011001011011101011001110101011"));
    assert(!decode_name_cert_holds("010111011011101101110101011"));

    assert(decode_name_cert_holds("00101110111011"));
    assert(decode_name_cert_holds("00101100101101011"));
    assert(!decode_name_cert_holds("0010111011101111"));
    assert(!decode_name_cert_holds("001011111011"));

    assert(decode_name_cert_holds("00010111111101011"));
    assert(decode_name_cert_holds("00010110111011101011"));
    assert(decode_name_cert_holds("000101111101101011"));
    assert(!decode_name_cert_holds("0001011111011101011"));
    assert(!decode_name_cert_holds("0001011011101110011"));

    assert(decode_name_cert_holds("00001011111110101011"));
    assert(decode_name_cert_holds("00001011010111001110101011"));
    assert(decode_name_cert_holds("000010111110110101011"));
    assert(!decode_name_cert_holds("0000101111101110101011"));
    assert(!decode_name_cert_holds("0000101101110111010011"));

    assert(decode_name_cert_holds("000001011101101011"));
    assert(decode_name_cert_holds("0000010110010110001011"));
    assert(decode_name_cert_holds("000001011000101100001011"));
    assert(!decode_name_cert_holds("00000101110111011"));
    assert(!decode_name_cert_holds("00000101100001011000001011"));
}

static void test_name_cert_basic_enum(void) {
    assert_name_cert_cases();
    assert_manifest_smoke("manifests/name_cert/name_cert_basic.enum.ct",
                          "1011101111111110101011");
    printf("  name_cert_basic.enum: 29/29 cases PASS\n");
}

static void test_name_cert_basic_algo(void) {
    assert_name_cert_cases();
    assert_name_cert_algo_ct_case("1011101111111110101011", 1);
    printf("  name_cert_basic.algo: 29/29 decoder cases + CT smoke PASS\n");
}

static void test_name_cert_algo_via_ct_runner(void) {
    const struct NameCertManifestCase {
        const char *input;
        int holds;
    } manifest_cases[] = {
        {"1011101111111110101011", 1},
        {"101101011011101101110101011", 1},
        {"10111011011101111100011", 1},
        {"10111011111011101110101011", 0},
        {"10111011011101101110101011", 0},
        {"01011101111111110101011", 1},
        {"0101100101101011101011001110101011", 1},
        {"01011101101110110111010011", 1},
        {"01011001011011101011001110101011", 0},
        {"010111011011101101110101011", 0},
        {"00101110111011", 1},
        {"00101100101101011", 1},
        {"0010111011101111", 0},
        {"001011111011", 0},
        {"00010111111101011", 1},
        {"00010110111011101011", 1},
        {"000101111101101011", 1},
        {"0001011111011101011", 0},
        {"0001011011101110011", 0},
        {"00001011111110101011", 1},
        {"00001011010111001110101011", 1},
        {"000010111110110101011", 1},
        {"0000101111101110101011", 0},
        {"0000101101110111010011", 0},
        {"000001011101101011", 1},
        {"0000010110010110001011", 1},
        {"000001011000101100001011", 1},
        {"00000101110111011", 0},
        {"00000101100001011000001011", 0}
    };
    char input[128];
    size_t checked = 0;

    for (size_t i = 0; i < sizeof(manifest_cases) / sizeof(manifest_cases[0]); i++) {
        assert_name_cert_algo_ct_case(manifest_cases[i].input,
                                      manifest_cases[i].holds);
    }

    for (size_t tag = 0; tag <= 1; tag++) {
        for (size_t bound = 0; bound <= 3; bound++) {
            for (size_t h_depth = 0; h_depth <= 2; h_depth++) {
                for (size_t k_depth = 0; k_depth <= 2; k_depth++) {
                    for (size_t r_depth = 0; r_depth <= 2; r_depth++) {
                        for (unsigned rel_mask = 0; rel_mask < 8; rel_mask++) {
                            uint8_t rel[3] = {
                                (uint8_t)((rel_mask >> 2) & 1u),
                                (uint8_t)((rel_mask >> 1) & 1u),
                                (uint8_t)(rel_mask & 1u)
                            };
                            unsigned h_value = h_depth == 0 ? 0u : ((1u << h_depth) - 1u);
                            unsigned k_value = k_depth == 0 ? 0u : (1u << (k_depth - 1));
                            unsigned r_value = r_depth == 0 ? 0u : ((1u << r_depth) - 1u);
                            assert(build_core_or_semantic_input(tag,
                                                                bound,
                                                                h_value,
                                                                h_depth,
                                                                k_value,
                                                                k_depth,
                                                                r_value,
                                                                r_depth,
                                                                rel,
                                                                input,
                                                                sizeof(input)));
                            assert_name_cert_algo_ct_case(input,
                                                          decode_name_cert_holds(input));
                            checked++;
                        }
                    }
                }
            }
        }
    }

    for (size_t thread = 0; thread <= 5; thread++) {
        for (size_t bound = 0; bound <= 3; bound++) {
            assert(build_seal_input(thread, bound, input, sizeof(input)));
            assert_name_cert_algo_ct_case(input, decode_name_cert_holds(input));
            checked++;
        }
    }

    for (size_t source_depth = 0; source_depth <= 3; source_depth++) {
        for (size_t target_depth = 0; target_depth <= 3; target_depth++) {
            for (uint8_t same = 0; same <= 1; same++) {
                for (uint8_t ledger = 0; ledger <= 1; ledger++) {
                    uint8_t rel[2] = {same, ledger};
                    unsigned source_value = source_depth == 0 ? 0u : ((1u << source_depth) - 1u);
                    unsigned target_value = target_depth == 0 ? 0u : (1u << (target_depth - 1));
                    assert(build_stable_or_composition_input(3,
                                                             source_value,
                                                             source_depth,
                                                             target_value,
                                                             target_depth,
                                                             rel,
                                                             2,
                                                             input,
                                                             sizeof(input)));
                    assert_name_cert_algo_ct_case(input,
                                                  decode_name_cert_holds(input));
                    checked++;
                }
            }
        }
    }

    for (size_t source_depth = 0; source_depth <= 3; source_depth++) {
        for (size_t target_depth = 0; target_depth <= 3; target_depth++) {
            for (uint8_t same = 0; same <= 1; same++) {
                for (uint8_t left_ledger = 0; left_ledger <= 1; left_ledger++) {
                    for (uint8_t right_ledger = 0; right_ledger <= 1; right_ledger++) {
                        uint8_t rel[3] = {same, left_ledger, right_ledger};
                        unsigned source_value = source_depth == 0 ? 0u : ((1u << source_depth) - 1u);
                        unsigned target_value = target_depth == 0 ? 0u : (1u << (target_depth - 1));
                        assert(build_stable_or_composition_input(4,
                                                                 source_value,
                                                                 source_depth,
                                                                 target_value,
                                                                 target_depth,
                                                                 rel,
                                                                 3,
                                                                 input,
                                                                 sizeof(input)));
                        assert_name_cert_algo_ct_case(input,
                                                      decode_name_cert_holds(input));
                        checked++;
                    }
                }
            }
        }
    }

    for (size_t left = 0; left <= 6; left++) {
        for (size_t right = 0; right <= 6; right++) {
            assert(build_mode_input(left, right, input, sizeof(input)));
            assert_name_cert_algo_ct_case(input, decode_name_cert_holds(input));
            checked++;
        }
    }

    printf("  name_cert_basic.algo CT runner: %zu bounded cases PASS\n",
           checked + sizeof(manifest_cases) / sizeof(manifest_cases[0]));
}

static void pipeline_smoke_test_name_cert_manifests(void) {
    assert_manifest_smoke("manifests/name_cert/name_cert_basic.enum.ct",
                          "1011101111111110101011");
    assert_name_cert_algo_ct_case("1011101111111110101011", 1);
    printf("  pipeline_smoke (enum halt-empty + algo certificate): PASS\n");
}

int main(void) {
    printf("== test_name_cert ==\n");
    test_name_cert_basic_enum();
    test_name_cert_basic_algo();
    test_name_cert_algo_via_ct_runner();
    pipeline_smoke_test_name_cert_manifests();
    printf("ALL test_name_cert assertions passed (bounded NameCert CT runner + decoder cross-check)\n");
    return 0;
}
