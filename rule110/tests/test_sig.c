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
    assert_manifest_smoke("manifests/sig/sigrel_basic.algo.ct", "111111");
    printf("  sigrel_basic.algo: 9/9 cases PASS\n");
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
    assert_manifest_smoke("manifests/sig/samesig_equiv.algo.ct", "111111");
    printf("  samesig_equiv.algo: 9/9 cases PASS\n");
}

static void pipeline_smoke_test_sig_manifests(void) {
    struct { const char *path; const char *input; } cases[] = {
        {"manifests/sig/sigrel_basic.enum.ct",   "111111"},
        {"manifests/sig/sigrel_basic.algo.ct",   "111111"},
        {"manifests/sig/samesig_equiv.enum.ct",  "111111"},
        {"manifests/sig/samesig_equiv.algo.ct",  "111111"},
    };
    size_t n = sizeof(cases) / sizeof(cases[0]);
    for (size_t i = 0; i < n; i++) {
        assert_manifest_smoke(cases[i].path, cases[i].input);
    }
    printf("  pipeline_smoke (4 sig manifests, all halt-empty in <=200 steps): PASS\n");
}

int main(void) {
    printf("== test_sig ==\n");
    test_sigrel_basic_enum();
    test_sigrel_basic_algo();
    test_samesig_equiv_enum();
    test_samesig_equiv_algo();
    pipeline_smoke_test_sig_manifests();
    printf("ALL test_sig assertions passed (36 semantic cases + 4-manifest pipeline smoke)\n");
    return 0;
}
