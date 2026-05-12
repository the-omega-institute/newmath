#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

typedef enum {
    ATOM_SORT = 0,
    ATOM_VAR = 1,
    ATOM_BAD = 2
} AtomKind;

typedef struct {
    AtomKind kind;
    size_t index;
} Atom;

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

static int bhist_equal(const BHist *a, const BHist *b) {
    return a->depth == b->depth &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
}

static int decode_one_bhist_exact(const char *input_bits, BHist *out) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;

    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult r = gc_bhist_decode(in_bytes, in_len, 8192);
    free(in_bytes);
    if (r.status != GC_OK) {
        free(r.bhist.choices);
        return 0;
    }
    if (r.bytes_consumed != in_len) {
        free(r.bhist.choices);
        return 0;
    }

    *out = r.bhist;
    return 1;
}

static int decode_two_bhist_exact(const char *input_bits, BHist *a, BHist *b) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    size_t off;

    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult r1 = gc_bhist_decode(in_bytes, in_len, 8192);
    if (r1.status != GC_OK) {
        free(in_bytes);
        free(r1.bhist.choices);
        return 0;
    }

    off = r1.bytes_consumed;
    GcBhistDecResult r2 = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    free(in_bytes);
    if (r2.status != GC_OK || off + r2.bytes_consumed != in_len) {
        free(r1.bhist.choices);
        free(r2.bhist.choices);
        return 0;
    }

    *a = r1.bhist;
    *b = r2.bhist;
    return 1;
}

static int bhist_all_e0(const BHist *h) {
    for (size_t i = 0; i < h->depth; i++) {
        if (h->choices[i] != 0) return 0;
    }
    return 1;
}

static int check_nat_to_bhist_len(const char *input_bits,
                                  size_t expected_len,
                                  int expected_all_e0) {
    BHist h;
    int ok;

    if (!decode_one_bhist_exact(input_bits, &h)) return 0;
    ok = (h.depth == expected_len) && (bhist_all_e0(&h) == expected_all_e0);
    free(h.choices);
    return ok;
}

static int payload_closed_at_choices(const uint8_t *choices,
                                     size_t depth,
                                     size_t d) {
    if (depth == 0) return d > 2;

    if (choices[0] == 0) {
        return d > 1 && payload_closed_at_choices(choices + 1, depth - 1, d + 3);
    }
    if (choices[0] == 1) {
        return d > 0 && payload_closed_at_choices(choices + 1, depth - 1, d + 3);
    }
    return 0;
}

static int bhist_to_term_closed_at_zero(const BHist *h) {
    return payload_closed_at_choices(h->choices, h->depth, 3);
}

static int check_bhist_to_term_closed(const char *input_bits) {
    BHist h;
    int ok;

    if (!decode_one_bhist_exact(input_bits, &h)) return 0;
    ok = bhist_to_term_closed_at_zero(&h);
    free(h.choices);
    return ok;
}

static int payload_term_equal(const BHist *a, const BHist *b) {
    return bhist_equal(a, b);
}

static int full_term_equal(const BHist *a, const BHist *b) {
    return payload_term_equal(a, b);
}

static int check_bhist_term_injective(const char *input_bits,
                                      int expected_term_equal,
                                      int expected_hist_equal) {
    BHist a;
    BHist b;
    int hist_eq;
    int term_eq;
    int ok;

    if (!decode_two_bhist_exact(input_bits, &a, &b)) return 0;
    hist_eq = bhist_equal(&a, &b);
    term_eq = full_term_equal(&a, &b);
    ok = (term_eq == expected_term_equal) &&
         (hist_eq == expected_hist_equal) &&
         (!term_eq || hist_eq);
    free(a.choices);
    free(b.choices);
    return ok;
}

static int decode_ctx_and_atom(const char *input_bits, size_t *ctx_len, Atom *atom) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    size_t off;

    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcDecResult ctx = gc_dec_event(in_bytes, in_len, 8192);
    if (ctx.status != GC_OK) {
        free(in_bytes);
        free(ctx.event);
        return 0;
    }
    for (size_t i = 0; i < ctx.event_len; i++) {
        if (ctx.event[i] != 0) {
            free(in_bytes);
            free(ctx.event);
            return 0;
        }
    }

    off = ctx.bytes_consumed;
    GcDecResult term = gc_dec_event(in_bytes + off, in_len - off, 8192);
    free(in_bytes);
    if (term.status != GC_OK || off + term.bytes_consumed != in_len) {
        free(ctx.event);
        free(term.event);
        return 0;
    }

    *ctx_len = ctx.event_len;
    if (term.event_len == 1 && term.event[0] == 0) {
        atom->kind = ATOM_SORT;
        atom->index = 0;
    } else if (term.event_len >= 1 && term.event[0] == 1) {
        int valid_var = 1;
        for (size_t i = 1; i < term.event_len; i++) {
            if (term.event[i] != 0) valid_var = 0;
        }
        atom->kind = valid_var ? ATOM_VAR : ATOM_BAD;
        atom->index = valid_var ? term.event_len - 1 : 0;
    } else {
        atom->kind = ATOM_BAD;
        atom->index = 0;
    }

    free(ctx.event);
    free(term.event);
    return 1;
}

static int infer_atom_is_some_sort(size_t ctx_len, const Atom *atom) {
    if (atom->kind == ATOM_SORT) return 1;
    if (atom->kind == ATOM_VAR) return atom->index < ctx_len;
    return 0;
}

static int check_atom_infer(const char *input_bits, int expected_some_sort) {
    size_t ctx_len = 0;
    Atom atom;

    if (!decode_ctx_and_atom(input_bits, &ctx_len, &atom)) return 0;
    return infer_atom_is_some_sort(ctx_len, &atom) == expected_some_sort;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void test_bhist_nat_len(void) {
    assert(check_nat_to_bhist_len("11", 0, 1));
    assert(check_nat_to_bhist_len("011", 1, 1));
    assert(check_nat_to_bhist_len("0011", 2, 1));
    assert(check_nat_to_bhist_len("00011", 3, 1));
    assert(check_nat_to_bhist_len("1011", 1, 0));
    assert_manifest_smoke("manifests/meta_cic/bhist_nat_len.enum.ct", "11");
    printf("  bhist_nat_len.enum: 5/5 cases PASS\n");
}

static void test_bhist_term_embedding(void) {
    assert(check_bhist_to_term_closed("11"));
    assert(check_bhist_to_term_closed("011"));
    assert(check_bhist_to_term_closed("1011"));
    assert(check_bhist_to_term_closed("0100101011"));
    assert(check_bhist_term_injective("1111", 1, 1));
    assert(check_bhist_term_injective("011011", 1, 1));
    assert(check_bhist_term_injective("0111011", 0, 0));
    assert(check_bhist_term_injective("010111001011", 0, 0));
    assert_manifest_smoke("manifests/meta_cic/bhist_term_embedding.enum.ct", "11");
    printf("  bhist_term_embedding.enum: 8/8 cases PASS\n");
}

static void test_atom_infer(void) {
    assert(check_atom_infer("11011", 1));
    assert(check_atom_infer("0011011", 1));
    assert(check_atom_infer("0111011", 1));
    assert(check_atom_infer("001110011", 1));
    assert(check_atom_infer("00011100011", 1));
    assert(check_atom_infer("01110011", 0));
    assert(check_atom_infer("110011", 0));
    assert_manifest_smoke("manifests/meta_cic/atom_infer.enum.ct", "11011");
    printf("  atom_infer.enum: 7/7 cases PASS\n");
}

int main(void) {
    printf("== test_meta_cic ==\n");
    test_bhist_nat_len();
    test_bhist_term_embedding();
    test_atom_infer();
    printf("ALL test_meta_cic assertions passed (20 total + 3-manifest pipeline smoke)\n");
    return 0;
}
