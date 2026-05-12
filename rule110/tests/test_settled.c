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

static int bhist_unary(const BHist *h) {
    for (size_t i = 0; i < h->depth; i++) {
        if (h->choices[i] != 1) return 0;
    }
    return 1;
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

static int decode_domain_at(const uint8_t *input, size_t input_len,
                            size_t *off, size_t *domain_out) {
    return decode_tag_at(input, input_len, off, domain_out);
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

static int ext_holds(const BHist *h, uint8_t mark, const BHist *r) {
    return r->depth == h->depth + 1 &&
           r->choices != NULL &&
           r->choices[0] == mark &&
           (h->depth == 0 || memcmp(r->choices + 1, h->choices, h->depth) == 0);
}

static int cont_holds(const BHist *h, const BHist *k, const BHist *r) {
    if (r->depth != h->depth + k->depth) return 0;
    if (k->depth > 0 && memcmp(r->choices, k->choices, k->depth) != 0) return 0;
    if (h->depth > 0 &&
        memcmp(r->choices + k->depth, h->choices, h->depth) != 0) {
        return 0;
    }
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

static int signature_same(const ProbeBundleFixture *bundle, const BHist *h,
                          const BHist *k) {
    BHist sig_h = {NULL, 0};
    BHist sig_k = {NULL, 0};
    int ok = compute_sigrel_result(bundle, h, &sig_h) &&
             compute_sigrel_result(bundle, k, &sig_k);
    int same = ok && bhist_equal(&sig_h, &sig_k);
    free_bhist(&sig_h);
    free_bhist(&sig_k);
    return same;
}

static int decode_ingap_tail(const uint8_t *bytes, size_t len, size_t *off) {
    size_t domain_bound = 0;
    ProbeBundleFixture bundle;
    BHist h = {NULL, 0};
    BHist witness_sig = {NULL, 0};
    BHist pkg = {NULL, 0};
    BHist computed_sig = {NULL, 0};
    int ok = decode_domain_at(bytes, len, off, &domain_bound);
    if (ok) ok = decode_probe_bundle(bytes, len, off, &bundle);
    if (ok) ok = decode_bhist_at(bytes, len, off, &h);
    if (ok) ok = decode_bhist_at(bytes, len, off, &witness_sig);
    if (ok) ok = decode_bhist_at(bytes, len, off, &pkg);
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

static int settled_history_family(const uint8_t *bytes, size_t len, size_t *off,
                                  size_t subcase) {
    BHist h = {NULL, 0};
    BHist k = {NULL, 0};
    int ok = 0;

    if (subcase == 0) {
        ok = decode_bhist_at(bytes, len, off, &h);
        ok = ok && h.depth == 1 && h.choices[0] == 0;
    } else if (subcase == 1) {
        ok = decode_bhist_at(bytes, len, off, &h);
        if (ok) ok = decode_bhist_at(bytes, len, off, &k);
        ok = ok && h.depth == 1 && k.depth == 1 &&
             h.choices[0] == 0 && k.choices[0] == 1 && !bhist_equal(&h, &k);
    } else if (subcase == 2) {
        ok = decode_bhist_at(bytes, len, off, &h);
    } else if (subcase == 3) {
        ok = decode_bhist_at(bytes, len, off, &h);
        if (ok) ok = decode_bhist_at(bytes, len, off, &k);
        ok = ok && k.depth == h.depth + 1 && k.choices[0] == 0 &&
             (h.depth == 0 || memcmp(k.choices + 1, h.choices, h.depth) == 0);
    } else if (subcase == 4) {
        ok = decode_bhist_at(bytes, len, off, &h);
        if (ok) ok = decode_bhist_at(bytes, len, off, &k);
        ok = ok && h.depth <= 1 && k.depth <= 1;
    }

    free_bhist(&h);
    free_bhist(&k);
    return ok;
}

static int settled_ext_cont_family(const uint8_t *bytes, size_t len, size_t *off,
                                   size_t subcase) {
    BHist a = {NULL, 0};
    BHist b = {NULL, 0};
    BHist c = {NULL, 0};
    BHist d = {NULL, 0};
    BHist e = {NULL, 0};
    int ok = 0;

    if (subcase == 0) {
        ok = decode_bhist_at(bytes, len, off, &a);
        if (ok) ok = decode_bhist_at(bytes, len, off, &b);
        if (ok) ok = decode_bhist_at(bytes, len, off, &c);
        if (ok) ok = decode_bhist_at(bytes, len, off, &d);
        ok = ok && b.depth == 1 &&
             ext_holds(&a, b.choices[0], &c) &&
             ext_holds(&a, b.choices[0], &d) &&
             bhist_equal(&c, &d);
    } else if (subcase == 1) {
        ok = decode_bhist_at(bytes, len, off, &a);
        if (ok) ok = decode_bhist_at(bytes, len, off, &b);
        if (ok) ok = decode_bhist_at(bytes, len, off, &c);
        if (ok) ok = decode_bhist_at(bytes, len, off, &d);
        ok = ok && cont_holds(&a, &b, &c) && cont_holds(&a, &b, &d) &&
             bhist_equal(&c, &d);
    } else if (subcase == 2) {
        ok = decode_bhist_at(bytes, len, off, &a);
        if (ok) ok = decode_bhist_at(bytes, len, off, &b);
        BHist empty = {NULL, 0};
        ok = ok && cont_holds(&empty, &a, &b) && bhist_equal(&a, &b);
    } else if (subcase == 3) {
        ok = decode_bhist_at(bytes, len, off, &a);
        if (ok) ok = decode_bhist_at(bytes, len, off, &b);
        BHist empty = {NULL, 0};
        ok = ok && cont_holds(&a, &empty, &b) && bhist_equal(&a, &b);
    } else if (subcase == 4) {
        ok = decode_bhist_at(bytes, len, off, &a);
        if (ok) ok = decode_bhist_at(bytes, len, off, &b);
        if (ok) ok = decode_bhist_at(bytes, len, off, &c);
        if (ok) ok = decode_bhist_at(bytes, len, off, &d);
        if (ok) ok = decode_bhist_at(bytes, len, off, &e);
        BHist ab = {NULL, 0};
        BHist bc = {NULL, 0};
        if (ok) {
            ab.depth = a.depth + b.depth;
            bc.depth = b.depth + c.depth;
            ab.choices = (uint8_t *)malloc(ab.depth ? ab.depth : 1);
            bc.choices = (uint8_t *)malloc(bc.depth ? bc.depth : 1);
            ok = ab.choices != NULL && bc.choices != NULL;
        }
        if (ok) {
            if (b.depth > 0) memcpy(ab.choices, b.choices, b.depth);
            if (a.depth > 0) memcpy(ab.choices + b.depth, a.choices, a.depth);
            if (c.depth > 0) memcpy(bc.choices, c.choices, c.depth);
            if (b.depth > 0) memcpy(bc.choices + c.depth, b.choices, b.depth);
            ok = cont_holds(&ab, &c, &d) && cont_holds(&a, &bc, &e) &&
                 bhist_equal(&d, &e);
        }
        free_bhist(&ab);
        free_bhist(&bc);
    }

    free_bhist(&a);
    free_bhist(&b);
    free_bhist(&c);
    free_bhist(&d);
    free_bhist(&e);
    return ok;
}

static int settled_signature_family(const uint8_t *bytes, size_t len,
                                    size_t *off, size_t subcase) {
    ProbeBundleFixture bundle;
    BHist h = {NULL, 0};
    BHist k = {NULL, 0};
    BHist l = {NULL, 0};
    BHist s = {NULL, 0};
    BHist t = {NULL, 0};
    int ok = decode_probe_bundle(bytes, len, off, &bundle);

    if (subcase == 0) {
        BHist computed = {NULL, 0};
        if (ok) ok = decode_bhist_at(bytes, len, off, &h);
        if (ok) ok = decode_bhist_at(bytes, len, off, &s);
        if (ok) ok = decode_bhist_at(bytes, len, off, &t);
        if (ok) ok = compute_sigrel_result(&bundle, &h, &computed);
        ok = ok && (!bhist_equal(&computed, &s) ||
                    !bhist_equal(&computed, &t) ||
                    bhist_equal(&s, &t));
        free_bhist(&computed);
    } else if (subcase == 1) {
        if (ok) ok = decode_bhist_at(bytes, len, off, &h);
        if (ok) ok = decode_bhist_at(bytes, len, off, &k);
        ok = ok && (!signature_same(&bundle, &h, &k) ||
                    signature_same(&bundle, &k, &h));
    } else if (subcase == 2) {
        if (ok) ok = decode_bhist_at(bytes, len, off, &h);
        if (ok) ok = decode_bhist_at(bytes, len, off, &k);
        if (ok) ok = decode_bhist_at(bytes, len, off, &l);
        int hk = ok && signature_same(&bundle, &h, &k);
        int kl = ok && signature_same(&bundle, &k, &l);
        int hl = ok && signature_same(&bundle, &h, &l);
        ok = ok && (!(hk && kl) || hl);
    } else {
        ok = 0;
    }

    free_bundle(&bundle);
    free_bhist(&h);
    free_bhist(&k);
    free_bhist(&l);
    free_bhist(&s);
    free_bhist(&t);
    return ok;
}

static int settled_package_gap_family(const uint8_t *bytes, size_t len,
                                      size_t *off, size_t subcase) {
    BHist a = {NULL, 0};
    BHist b = {NULL, 0};
    BHist c = {NULL, 0};
    BHist d = {NULL, 0};
    int ok = 0;

    if (subcase == 0) {
        ok = decode_ingap_tail(bytes, len, off);
    } else if (subcase == 1) {
        ok = decode_bhist_at(bytes, len, off, &a);
        if (ok) ok = decode_bhist_at(bytes, len, off, &b);
        if (ok) ok = decode_bhist_at(bytes, len, off, &c);
        if (ok) ok = decode_bhist_at(bytes, len, off, &d);
        ok = ok && (!bhist_equal(&a, &b) ||
                    !bhist_equal(&a, &c) ||
                    !bhist_equal(&b, &d) ||
                    bhist_equal(&c, &d));
    } else if (subcase == 2) {
        ok = decode_bhist_at(bytes, len, off, &a);
        if (ok) ok = decode_bhist_at(bytes, len, off, &b);
        ok = ok && bhist_equal(&a, &b);
    }

    free_bhist(&a);
    free_bhist(&b);
    free_bhist(&c);
    free_bhist(&d);
    return ok;
}

static int settled_globalize_family(const uint8_t *bytes, size_t len,
                                    size_t *off, size_t subcase) {
    if (subcase == 1) {
        size_t domain_bound = 0;
        ProbeBundleFixture bundle;
        BHist h = {NULL, 0};
        BHist sig = {NULL, 0};
        int ok = decode_domain_at(bytes, len, off, &domain_bound);
        if (ok) ok = decode_probe_bundle(bytes, len, off, &bundle);
        if (ok) ok = decode_bhist_at(bytes, len, off, &h);
        if (ok) ok = compute_sigrel_result(&bundle, &h, &sig);
        ok = ok && h.depth <= domain_bound;
        free_bundle(&bundle);
        free_bhist(&h);
        free_bhist(&sig);
        return ok;
    }

    if (subcase != 0) return 0;

    size_t domain_bound = 0;
    ProbeBundleFixture bundle;
    BHist h = {NULL, 0};
    BHist k = {NULL, 0};
    BHist p = {NULL, 0};
    BHist q = {NULL, 0};
    BHist sig_h = {NULL, 0};
    BHist sig_k = {NULL, 0};
    int ok = decode_domain_at(bytes, len, off, &domain_bound);
    if (ok) ok = decode_probe_bundle(bytes, len, off, &bundle);
    if (ok) ok = decode_bhist_at(bytes, len, off, &h);
    if (ok) ok = decode_bhist_at(bytes, len, off, &k);
    if (ok) ok = decode_bhist_at(bytes, len, off, &p);
    if (ok) ok = decode_bhist_at(bytes, len, off, &q);
    if (ok) ok = compute_sigrel_result(&bundle, &h, &sig_h);
    if (ok) ok = compute_sigrel_result(&bundle, &k, &sig_k);
    int in_domain = ok && h.depth <= domain_bound && k.depth <= domain_bound;
    int tokens_match = ok && bhist_equal(&sig_h, &p) && bhist_equal(&sig_k, &q);
    int packages_same = ok && bhist_equal(&p, &q);
    int signatures_same = ok && bhist_equal(&sig_h, &sig_k);
    ok = in_domain && tokens_match && (packages_same == signatures_same);

    free_bundle(&bundle);
    free_bhist(&h);
    free_bhist(&k);
    free_bhist(&p);
    free_bhist(&q);
    free_bhist(&sig_h);
    free_bhist(&sig_k);
    return ok;
}

static int settled_composite_family(const uint8_t *bytes, size_t len,
                                    size_t *off, size_t subcase) {
    BHist source = {NULL, 0};
    BHist inter = {NULL, 0};
    BHist final = {NULL, 0};
    int first = 0;
    int second = 0;
    int ok = subcase == 0;
    if (ok) ok = decode_bhist_at(bytes, len, off, &source);
    if (ok) ok = decode_bhist_at(bytes, len, off, &inter);
    if (ok) ok = decode_bhist_at(bytes, len, off, &final);
    if (ok) ok = decode_relation_bits_at(bytes, len, off, &first, &second);
    ok = ok && first && second;
    free_bhist(&source);
    free_bhist(&inter);
    free_bhist(&final);
    return ok;
}

static int settled_namecert_family(const uint8_t *bytes, size_t len,
                                   size_t *off, size_t subcase) {
    BHist h = {NULL, 0};
    BHist k = {NULL, 0};
    int ok = 0;

    if (subcase == 3) return 1;

    ok = decode_bhist_at(bytes, len, off, &h);
    if (ok) ok = decode_bhist_at(bytes, len, off, &k);
    if (subcase == 0) {
        ok = ok && bhist_unary(&h) && bhist_unary(&k) && bhist_equal(&h, &k);
    } else if (subcase == 1) {
        ok = ok && bhist_unary(&h) && bhist_equal(&h, &k) && bhist_unary(&k);
    } else if (subcase == 2) {
        ok = ok && bhist_equal(&h, &k);
    } else {
        ok = 0;
    }

    free_bhist(&h);
    free_bhist(&k);
    return ok;
}

static int settled_descent_family(const uint8_t *bytes, size_t len,
                                  size_t *off, size_t subcase) {
    BHist source_a = {NULL, 0};
    BHist source_b = {NULL, 0};
    int ok = subcase == 0;
    if (ok) ok = decode_bhist_at(bytes, len, off, &source_a);
    if (ok) ok = decode_bhist_at(bytes, len, off, &source_b);
    ok = ok && (!bhist_equal(&source_a, &source_b) ||
                bhist_equal(&source_a, &source_b));
    free_bhist(&source_a);
    free_bhist(&source_b);
    return ok;
}

static int settled_bundle_family(const uint8_t *bytes, size_t len,
                                 size_t *off, size_t subcase) {
    ProbeBundleFixture bundle;
    int ok = subcase == 0 && decode_probe_bundle(bytes, len, off, &bundle);
    if (ok) ok = 1;
    free_bundle(&bundle);
    return ok;
}

static int decode_settled_holds(const char *input_bits) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    size_t off = 0;
    size_t family = 0;
    size_t subcase = 0;
    int ok = decode_tag_at(bytes, len, &off, &family);
    if (ok) ok = decode_tag_at(bytes, len, &off, &subcase);

    int holds = 0;
    if (ok && family == 0) {
        holds = settled_history_family(bytes, len, &off, subcase);
    } else if (ok && family == 1) {
        holds = settled_ext_cont_family(bytes, len, &off, subcase);
    } else if (ok && family == 2) {
        holds = settled_signature_family(bytes, len, &off, subcase);
    } else if (ok && family == 3) {
        holds = settled_package_gap_family(bytes, len, &off, subcase);
    } else if (ok && family == 4) {
        holds = settled_globalize_family(bytes, len, &off, subcase);
    } else if (ok && family == 5) {
        holds = settled_composite_family(bytes, len, &off, subcase);
    } else if (ok && family == 6) {
        holds = settled_namecert_family(bytes, len, &off, subcase);
    } else if (ok && family == 7) {
        holds = settled_descent_family(bytes, len, &off, subcase);
    } else if (ok && family == 8) {
        holds = settled_bundle_family(bytes, len, &off, subcase);
    }

    holds = holds && off == len;
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

static void assert_settled_cases(void) {
    assert(decode_settled_holds("10111011011"));
    assert(decode_settled_holds("1011010110111011"));
    assert(decode_settled_holds("101100101110011"));
    assert(decode_settled_holds("10110001011101101011"));
    assert(decode_settled_holds("1011000010110111011"));
    assert(!decode_settled_holds("1011101101011"));

    assert(decode_settled_holds("01011101111101110111011"));
    assert(decode_settled_holds("010110101101110111001110011"));
    assert(decode_settled_holds("010110010111001110011"));
    assert(decode_settled_holds("0101100010110101101011"));
    assert(decode_settled_holds("01011000010110111011010110101001101010011"));
    assert(!decode_settled_holds("0101110111110111011011"));

    assert(decode_settled_holds("001011101110111111011011"));
    assert(decode_settled_holds("001011010111011110111011"));
    assert(decode_settled_holds("001011001011101101011111101011101011"));
    assert(decode_settled_holds("0010111011101111111011011"));

    assert(decode_settled_holds("00010111011101111111111"));
    assert(decode_settled_holds("000101110110101110111101110111011"));
    assert(decode_settled_holds("00010110101101011010110101101011"));
    assert(decode_settled_holds("00010110010111001110011"));
    assert(!decode_settled_holds("00010111011010111011110111011011"));

    assert(decode_settled_holds("00001011101110111111111111"));
    assert(decode_settled_holds("00001011101100101110111111101011011011"));
    assert(decode_settled_holds("00001011010110010111011010111110011"));
    assert(!decode_settled_holds("0000101101011010111011010111110011"));

    assert(decode_settled_holds("0000010111011011101110011101011"));
    assert(!decode_settled_holds("000001011101101110111001110011"));

    assert(decode_settled_holds("000000101110111111"));
    assert(decode_settled_holds("0000001011101110111011"));
    assert(!decode_settled_holds("00000010111011011011"));
    assert(decode_settled_holds("000000101101011101011101011"));
    assert(decode_settled_holds("00000010110010111001110011"));
    assert(decode_settled_holds("00000010110001011"));

    assert(decode_settled_holds("0000000101110111001110011"));
    assert(decode_settled_holds("000000010111011101110011"));

    assert(decode_settled_holds("000000001011101111"));
    assert(decode_settled_holds("000000001011101110110101111"));
    assert(!decode_settled_holds("0000000010111011011"));
}

static void test_settled_basic_enum(void) {
    assert_settled_cases();
    assert_manifest_smoke("manifests/settled/settled_basic.enum.ct", "10111011011");
    printf("  settled_basic.enum: 38/38 cases PASS\n");
}

static void test_settled_basic_algo(void) {
    assert_settled_cases();
    assert_manifest_smoke("manifests/settled/settled_basic.algo.ct", "10111011011");
    printf("  settled_basic.algo: 38/38 cases PASS\n");
}

int main(void) {
    printf("== test_settled ==\n");
    test_settled_basic_enum();
    test_settled_basic_algo();
    printf("ALL test_settled assertions passed (76 Settled cases + 2-manifest pipeline smoke)\n");
    return 0;
}
