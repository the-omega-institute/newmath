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
    assert_manifest_smoke("manifests/gap/gap_basic.algo.ct", "011101111111111");
    printf("  gap_basic.algo: 14/14 cases PASS\n");
}

int main(void) {
    printf("== test_gap ==\n");
    test_gap_basic_enum();
    test_gap_basic_algo();
    printf("ALL test_gap assertions passed (28 Gap cases + 2-manifest pipeline smoke)\n");
    return 0;
}
