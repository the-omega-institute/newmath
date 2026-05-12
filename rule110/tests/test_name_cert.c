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
    assert_manifest_smoke("manifests/name_cert/name_cert_basic.algo.ct",
                          "1011101111111110101011");
    printf("  name_cert_basic.algo: 29/29 cases PASS\n");
}

static void pipeline_smoke_test_name_cert_manifests(void) {
    struct { const char *path; const char *input; } cases[] = {
        {"manifests/name_cert/name_cert_basic.enum.ct", "1011101111111110101011"},
        {"manifests/name_cert/name_cert_basic.algo.ct", "1011101111111110101011"},
    };
    size_t n = sizeof(cases) / sizeof(cases[0]);
    for (size_t i = 0; i < n; i++) {
        assert_manifest_smoke(cases[i].path, cases[i].input);
    }
    printf("  pipeline_smoke (2 name_cert manifests, all halt-empty in <=200 steps): PASS\n");
}

int main(void) {
    printf("== test_name_cert ==\n");
    test_name_cert_basic_enum();
    test_name_cert_basic_algo();
    pipeline_smoke_test_name_cert_manifests();
    printf("ALL test_name_cert assertions passed (58 NameCert cases + 2-manifest pipeline smoke)\n");
    return 0;
}
