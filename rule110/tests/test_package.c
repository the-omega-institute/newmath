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

typedef struct {
    unsigned value;
    size_t depth;
} HistFixture;

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

static size_t append_unary_tag(char *dst, size_t off, size_t tag) {
    for (size_t i = 0; i < tag; i++) {
        dst[off++] = '0';
    }
    return append_bit_chars(dst, off, "1011", 4);
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

static size_t append_bhist_fixture(char *out,
                                   size_t off,
                                   size_t out_cap,
                                   HistFixture h) {
    uint8_t choices[4];
    char bits[16];
    size_t len;

    make_bhist_choices(h.value, h.depth, choices);
    len = encode_bhist_bits(choices, h.depth, bits, sizeof(bits));
    if (len == 0 || off + len + 1 > out_cap) return 0;
    return append_bit_chars(out, off, bits, len);
}

static size_t append_empty_bundle(char *out, size_t off, size_t out_cap) {
    if (off + 6 + 1 > out_cap) return 0;
    return append_bit_chars(out, off, "101011", 6);
}

static size_t append_claim_bits(char *out,
                                size_t off,
                                size_t out_cap,
                                int claimed_psame,
                                int claimed_hsame) {
    const char *p = claimed_psame ? "10" : "0";
    const char *h = claimed_hsame ? "10" : "0";

    if (off + strlen(p) + strlen(h) + 2 + 1 > out_cap) return 0;
    off = append_bit_chars(out, off, p, strlen(p));
    off = append_bit_chars(out, off, h, strlen(h));
    return append_bit_chars(out, off, "11", 2);
}

static int build_token_input(HistFixture s,
                             HistFixture p,
                             char *out,
                             size_t out_cap) {
    size_t off = append_unary_tag(out, 0, 0);
    off = append_empty_bundle(out, off, out_cap);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, s);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, p);
    return off != 0;
}

static int build_psame_input(HistFixture s,
                             HistFixture t,
                             HistFixture p,
                             HistFixture q,
                             char *out,
                             size_t out_cap) {
    size_t off = append_unary_tag(out, 0, 1);
    off = append_empty_bundle(out, off, out_cap);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, s);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, t);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, p);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, q);
    return off != 0;
}

static int build_classification_input(HistFixture s,
                                      HistFixture t,
                                      HistFixture p,
                                      HistFixture q,
                                      int claimed_psame,
                                      int claimed_hsame,
                                      char *out,
                                      size_t out_cap) {
    size_t off = append_unary_tag(out, 0, 2);
    off = append_empty_bundle(out, off, out_cap);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, s);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, t);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, p);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, q);
    if (off == 0) return 0;
    off = append_claim_bits(out, off, out_cap, claimed_psame, claimed_hsame);
    return off != 0;
}

static int build_chain_input(HistFixture a,
                             HistFixture b,
                             HistFixture c,
                             HistFixture p,
                             HistFixture q,
                             HistFixture r,
                             char *out,
                             size_t out_cap) {
    size_t off = append_unary_tag(out, 0, 3);
    off = append_empty_bundle(out, off, out_cap);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, a);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, b);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, c);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, p);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, q);
    if (off == 0) return 0;
    off = append_bhist_fixture(out, off, out_cap, r);
    return off != 0;
}

static char *package_algo_certificate(const char *input_bits) {
    size_t input_len = strlen(input_bits);
    size_t ones = 0;
    char *out;
    size_t o = 0;

    assert(input_len <= 128);
    for (size_t i = 0; i < input_len; i++) {
        assert(input_bits[i] == '0' || input_bits[i] == '1');
        if (input_bits[i] == '1') ones++;
    }

    out = (char *)malloc(ones * 8 + 1);
    assert(out != NULL);
    for (size_t i = 0; i < input_len; i++) {
        if (input_bits[i] == '1') {
            out[o++] = '1';
            for (int bit = 6; bit >= 0; bit--) {
                out[o++] = ((i >> (size_t)bit) & 1u) ? '1' : '0';
            }
        }
    }
    out[o] = '\0';
    return out;
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
                         size_t *off, size_t *tag_out) {
    GcDecResult event = gc_dec_event(input + *off, input_len - *off, 8192);
    if (event.status != GC_OK) {
        free(event.event);
        return 0;
    }
    int ok = decode_unary_event_as_nat(event.event, event.event_len, tag_out);
    if (ok) *off += event.bytes_consumed;
    free(event.event);
    return ok;
}

static int decode_probe_bundle_at(const uint8_t *input, size_t input_len,
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

        if (event.event_len == 2 && event.event[0] == 1 && event.event[1] == 1) {
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

static int decode_claim_bits_at(const uint8_t *input, size_t input_len,
                                size_t *off, int *claimed_psame,
                                int *claimed_hsame) {
    GcDecResult event = gc_dec_event(input + *off, input_len - *off, 8192);
    if (event.status != GC_OK) {
        free(event.event);
        return 0;
    }
    int ok = event.event_len == 2 &&
             (event.event[0] == 0 || event.event[0] == 1) &&
             (event.event[1] == 0 || event.event[1] == 1);
    if (ok) {
        *claimed_psame = event.event[0] == 1;
        *claimed_hsame = event.event[1] == 1;
        *off += event.bytes_consumed;
    }
    free(event.event);
    return ok;
}

static int tok_intro_holds(const BHist *source, const BHist *pkg) {
    return bhist_equal(source, pkg);
}

static int psame_holds(const BHist *s, const BHist *t,
                       const BHist *p, const BHist *q) {
    return tok_intro_holds(s, p) && tok_intro_holds(t, q) && bhist_equal(s, t);
}

static int decode_token_holds_bytes(const uint8_t *bytes, size_t len, size_t off) {
    ProbeBundleFixture bundle;
    BHist source = {NULL, 0};
    BHist pkg = {NULL, 0};
    int ok = decode_probe_bundle_at(bytes, len, &off, &bundle);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &source);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &pkg);
    if (ok) ok = (off == len);

    int holds = ok && tok_intro_holds(&source, &pkg);
    free_bundle(&bundle);
    free_bhist(&source);
    free_bhist(&pkg);
    return holds;
}

static int decode_psame_holds_bytes(const uint8_t *bytes, size_t len, size_t off) {
    ProbeBundleFixture bundle;
    BHist s = {NULL, 0};
    BHist t = {NULL, 0};
    BHist p = {NULL, 0};
    BHist q = {NULL, 0};
    int ok = decode_probe_bundle_at(bytes, len, &off, &bundle);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &s);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &t);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &p);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &q);
    if (ok) ok = (off == len);

    int holds = ok && psame_holds(&s, &t, &p, &q);
    free_bundle(&bundle);
    free_bhist(&s);
    free_bhist(&t);
    free_bhist(&p);
    free_bhist(&q);
    return holds;
}

static int decode_classification_holds_bytes(const uint8_t *bytes, size_t len,
                                             size_t off) {
    ProbeBundleFixture bundle;
    BHist s = {NULL, 0};
    BHist t = {NULL, 0};
    BHist p = {NULL, 0};
    BHist q = {NULL, 0};
    int claimed_psame = 0;
    int claimed_hsame = 0;
    int ok = decode_probe_bundle_at(bytes, len, &off, &bundle);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &s);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &t);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &p);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &q);
    if (ok) ok = decode_claim_bits_at(bytes, len, &off, &claimed_psame, &claimed_hsame);
    if (ok) ok = (off == len);

    int introduced = ok && tok_intro_holds(&s, &p) && tok_intro_holds(&t, &q);
    int actual_hsame = introduced && bhist_equal(&s, &t);
    int actual_psame = introduced && psame_holds(&s, &t, &p, &q);
    int holds = introduced &&
                claimed_psame == actual_psame &&
                claimed_hsame == actual_hsame;

    free_bundle(&bundle);
    free_bhist(&s);
    free_bhist(&t);
    free_bhist(&p);
    free_bhist(&q);
    return holds;
}

static int decode_chain_holds_bytes(const uint8_t *bytes, size_t len, size_t off) {
    ProbeBundleFixture bundle;
    BHist a = {NULL, 0};
    BHist b = {NULL, 0};
    BHist c = {NULL, 0};
    BHist p = {NULL, 0};
    BHist q = {NULL, 0};
    BHist r = {NULL, 0};
    int ok = decode_probe_bundle_at(bytes, len, &off, &bundle);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &a);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &b);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &c);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &p);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &q);
    if (ok) ok = decode_bhist_at(bytes, len, &off, &r);
    if (ok) ok = (off == len);

    int left = ok && psame_holds(&a, &b, &p, &q);
    int right = ok && psame_holds(&b, &c, &q, &r);
    int outer = ok && psame_holds(&a, &c, &p, &r);
    int holds = left && right && outer;

    free_bundle(&bundle);
    free_bhist(&a);
    free_bhist(&b);
    free_bhist(&c);
    free_bhist(&p);
    free_bhist(&q);
    free_bhist(&r);
    return holds;
}

static int decode_package_holds(const char *input_bits) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    size_t off = 0;
    size_t tag = 0;
    int ok = decode_tag_at(bytes, len, &off, &tag);
    int holds = 0;
    if (ok && tag == 0) {
        holds = decode_token_holds_bytes(bytes, len, off);
    } else if (ok && tag == 1) {
        holds = decode_psame_holds_bytes(bytes, len, off);
    } else if (ok && tag == 2) {
        holds = decode_classification_holds_bytes(bytes, len, off);
    } else if (ok && tag == 3) {
        holds = decode_chain_holds_bytes(bytes, len, off);
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

static void assert_package_algo_ct_case(const char *input_bits, int expected_holds) {
    char *expected = package_algo_certificate(input_bits);
    MrResult r;

    assert(decode_package_holds(input_bits) == expected_holds);
    r = mr_run_ct_manifest("manifests/package/package_basic.algo.ct",
                           input_bits,
                           expected,
                           strlen(input_bits));
    if (r != MR_PASS) {
        fprintf(stderr, "package_basic.algo CT FAIL on input=%s expected=%s result=%d\n",
                input_bits, expected, (int)r);
    }
    free(expected);
    assert(r == MR_PASS);
}

static int hist_fixture_equal(HistFixture a, HistFixture b) {
    return a.depth == b.depth && a.value == b.value;
}

static int expected_token_fixture(HistFixture s, HistFixture p) {
    return hist_fixture_equal(s, p);
}

static int expected_psame_fixture(HistFixture s,
                                  HistFixture t,
                                  HistFixture p,
                                  HistFixture q) {
    return hist_fixture_equal(s, p) &&
           hist_fixture_equal(t, q) &&
           hist_fixture_equal(s, t);
}

static void test_package_algo_ct_runner_cases(void) {
    struct { const char *input; int holds; } cases[] = {
        {"10111010111111", 1},
        {"101110110010111010110101101011", 1},
        {"10111010110111011", 0},
        {"1011111111", 0},
        {"101110101111111011", 0},
        {"0101110101111111111", 1},
        {"010110101110101101011010110101101011", 1},
        {"010110101110101101011010110101101011", 1},
        {"0101110101101110110111011", 0},
        {"010111010110110110111011", 0},
        {"0101110101111111111011", 0},
        {"00101110101111111111101011", 1},
        {"0010111011101011011101101110110011", 1},
        {"0010111010111111111101011", 0},
        {"0010111010110111011011101101011", 0},
        {"0010111010110110110111011101011", 0},
        {"0001011101011100111001110011100111001110011", 1},
        {"000101110101101101110110110111011", 0},
        {"00001011101011", 0},
    };
    size_t n = sizeof(cases) / sizeof(cases[0]);

    for (size_t i = 0; i < n; i++) {
        assert_package_algo_ct_case(cases[i].input, cases[i].holds);
    }
    printf("  package_basic.algo.ct_runner: 19/19 cases PASS\n");
}

static void test_package_algo_small_sweep(void) {
    HistFixture hist[] = {
        {0, 0},
        {0, 1},
        {1, 1},
        {0, 2},
        {1, 2},
        {2, 2},
        {3, 2},
    };
    size_t hist_n = sizeof(hist) / sizeof(hist[0]);
    char input[128];
    size_t checked = 0;

    for (size_t s = 0; s < hist_n; s++) {
        for (size_t p = 0; p < hist_n; p++) {
            assert(build_token_input(hist[s], hist[p], input, sizeof(input)));
            assert_package_algo_ct_case(input, expected_token_fixture(hist[s], hist[p]));
            checked++;
        }
    }

    for (size_t s = 0; s < hist_n; s++) {
        for (size_t t = 0; t < hist_n; t++) {
            for (size_t p = 0; p < hist_n; p++) {
                size_t q = (s + t + p) % hist_n;
                int expected = expected_psame_fixture(hist[s], hist[t], hist[p], hist[q]);
                assert(build_psame_input(hist[s], hist[t], hist[p], hist[q],
                                         input, sizeof(input)));
                assert_package_algo_ct_case(input, expected);
                checked++;
            }
        }
    }

    for (size_t s = 0; s < hist_n; s++) {
        for (size_t t = 0; t < hist_n; t++) {
            size_t p = s;
            size_t q = t;
            int actual = expected_psame_fixture(hist[s], hist[t], hist[p], hist[q]);
            assert(build_classification_input(hist[s], hist[t], hist[p], hist[q],
                                              actual, actual, input, sizeof(input)));
            assert_package_algo_ct_case(input, 1);
            checked++;
        }
    }

    for (size_t a = 0; a < hist_n; a++) {
        size_t b = a;
        size_t c = a;
        assert(build_chain_input(hist[a], hist[b], hist[c],
                                 hist[a], hist[b], hist[c],
                                 input, sizeof(input)));
        assert_package_algo_ct_case(input, 1);
        checked++;

        c = (a + 1) % hist_n;
        assert(build_chain_input(hist[a], hist[b], hist[c],
                                 hist[a], hist[b], hist[c],
                                 input, sizeof(input)));
        assert_package_algo_ct_case(input, 0);
        checked++;
    }

    printf("  package_basic.algo.small_sweep: %zu bounded CT cases PASS\n", checked);
}

static void test_package_basic_enum(void) {
    assert(decode_package_holds("10111010111111"));
    assert(decode_package_holds("101110110010111010110101101011"));
    assert(!decode_package_holds("10111010110111011"));
    assert(!decode_package_holds("1011111111"));
    assert(!decode_package_holds("101110101111111011"));

    assert(decode_package_holds("0101110101111111111"));
    assert(decode_package_holds("010110101110101101011010110101101011"));
    assert(decode_package_holds("010110101110101101011010110101101011"));
    assert(!decode_package_holds("0101110101101110110111011"));
    assert(!decode_package_holds("010111010110110110111011"));
    assert(!decode_package_holds("0101110101111111111011"));

    assert(decode_package_holds("00101110101111111111101011"));
    assert(decode_package_holds("0010111011101011011101101110110011"));
    assert(!decode_package_holds("0010111010111111111101011"));
    assert(!decode_package_holds("0010111010110111011011101101011"));
    assert(!decode_package_holds("0010111010110110110111011101011"));

    assert(decode_package_holds("0001011101011100111001110011100111001110011"));
    assert(!decode_package_holds("000101110101101101110110110111011"));
    assert(!decode_package_holds("00001011101011"));

    assert_manifest_smoke("manifests/package/package_basic.enum.ct",
                          "10111010111111");
    printf("  package_basic.enum: 19/19 cases PASS\n");
}

static void test_package_basic_algo(void) {
    assert(decode_package_holds("10111010111111"));
    assert(decode_package_holds("101110110010111010110101101011"));
    assert(!decode_package_holds("10111010110111011"));
    assert(!decode_package_holds("1011111111"));
    assert(!decode_package_holds("101110101111111011"));

    assert(decode_package_holds("0101110101111111111"));
    assert(decode_package_holds("010110101110101101011010110101101011"));
    assert(decode_package_holds("010110101110101101011010110101101011"));
    assert(!decode_package_holds("0101110101101110110111011"));
    assert(!decode_package_holds("010111010110110110111011"));
    assert(!decode_package_holds("0101110101111111111011"));

    assert(decode_package_holds("00101110101111111111101011"));
    assert(decode_package_holds("0010111011101011011101101110110011"));
    assert(!decode_package_holds("0010111010111111111101011"));
    assert(!decode_package_holds("0010111010110111011011101101011"));
    assert(!decode_package_holds("0010111010110110110111011101011"));

    assert(decode_package_holds("0001011101011100111001110011100111001110011"));
    assert(!decode_package_holds("000101110101101101110110110111011"));
    assert(!decode_package_holds("00001011101011"));

    test_package_algo_ct_runner_cases();
    test_package_algo_small_sweep();
    printf("  package_basic.algo: 19/19 cases PASS\n");
}

static void pipeline_smoke_test_package_manifests(void) {
    assert_manifest_smoke("manifests/package/package_basic.enum.ct",
                          "10111010111111");
    assert_package_algo_ct_case("10111010111111", 1);
    printf("  pipeline_smoke (2 package manifests): PASS\n");
}

int main(void) {
    printf("== test_package ==\n");
    test_package_basic_enum();
    test_package_basic_algo();
    pipeline_smoke_test_package_manifests();
    printf("ALL test_package assertions passed (38 Package cases + bounded CT certificates)\n");
    return 0;
}
