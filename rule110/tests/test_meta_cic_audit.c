#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>

#define MAX_CASES 32
#define MAX_LINE 4096
#define MAX_TEXT 2048

typedef struct {
    char name[128];
    char input[MAX_TEXT];
    char line[MAX_LINE];
} AuditCase;

typedef struct {
    AuditCase cases[MAX_CASES];
    size_t count;
    size_t assertions;
} AuditManifest;

static char *trim_ascii(char *s) {
    char *end;
    while (*s && isspace((unsigned char)*s)) s++;
    end = s + strlen(s);
    while (end > s && isspace((unsigned char)end[-1])) end--;
    *end = '\0';
    return s;
}

static int field_value(const char *line, const char *key, char *out, size_t cap) {
    char needle[64];
    const char *p;
    const char *end;
    size_t n;
    if (snprintf(needle, sizeof(needle), "%s=", key) >= (int)sizeof(needle)) return 0;
    p = strstr(line, needle);
    if (p == NULL) return 0;
    p += strlen(needle);
    while (*p && isspace((unsigned char)*p)) p++;
    end = p;
    while (*end && *end != ';' && !isspace((unsigned char)*end)) end++;
    n = (size_t)(end - p);
    if (n + 1 > cap) return 0;
    memcpy(out, p, n);
    out[n] = '\0';
    return 1;
}

static int parse_manifest(const char *path, AuditManifest *out) {
    FILE *f = fopen(path, "r");
    char line[MAX_LINE];
    int saw_prod = 0;
    int saw_assert = 0;
    if (f == NULL) return 0;
    memset(out, 0, sizeof(*out));
    while (fgets(line, sizeof(line), f) != NULL) {
        char raw[MAX_LINE];
        char *s;
        memcpy(raw, line, strlen(line) + 1);
        s = trim_ascii(line);
        if (s[0] == '\0' || s[0] == '#') continue;
        if (strncmp(s, "PRODUCTIONS ", 12) == 0) {
            saw_prod = strcmp(trim_ascii(s + 12), "0") == 0;
        } else if (strncmp(s, "ASSERTIONS ", 11) == 0) {
            out->assertions = (size_t)strtoul(s + 11, NULL, 10);
            saw_assert = 1;
        } else if (strncmp(s, "case ", 5) == 0) {
            char *colon;
            assert(out->count < MAX_CASES);
            colon = strchr(s + 5, ':');
            assert(colon != NULL);
            *colon = '\0';
            strcpy(out->cases[out->count].name, trim_ascii(s + 5));
            assert(field_value(raw, "input", out->cases[out->count].input,
                               sizeof(out->cases[out->count].input)));
            for (size_t i = 0; out->cases[out->count].input[i] != '\0'; i++) {
                assert(out->cases[out->count].input[i] == '0' ||
                       out->cases[out->count].input[i] == '1');
            }
            strcpy(out->cases[out->count].line, raw);
            out->count++;
        }
    }
    fclose(f);
    return saw_prod && saw_assert && out->assertions == out->count && out->count >= 3;
}

static int compare_files(const char *a, const char *b) {
    FILE *fa = fopen(a, "rb");
    FILE *fb = fopen(b, "rb");
    int ca;
    int cb;
    assert(fa != NULL);
    assert(fb != NULL);
    do {
        ca = fgetc(fa);
        cb = fgetc(fb);
        if (ca != cb) {
            fclose(fa);
            fclose(fb);
            return 0;
        }
    } while (ca != EOF && cb != EOF);
    fclose(fa);
    fclose(fb);
    return 1;
}

static void assert_generate_idempotent(const char *enum_path, const char *r110_path,
                                       const char *tmp_path) {
    char command[1024];
    assert(snprintf(command, sizeof(command), "./encoder/generate_r110 %s %s > /dev/null",
                    enum_path, tmp_path) < (int)sizeof(command));
    assert(system(command) == 0);
    assert(compare_files(r110_path, tmp_path));
    remove(tmp_path);
}

static void assert_r110_payloads(const char *path, size_t expected_cases) {
    FILE *f = fopen(path, "r");
    char line[MAX_LINE];
    size_t cases = 0;
    int saw_header = 0;
    assert(f != NULL);
    while (fgets(line, sizeof(line), f) != NULL) {
        char input[MAX_TEXT];
        char initial[MAX_TEXT];
        char expected[MAX_TEXT];
        char steps[32];
        char start_text[32];
        char len_text[32];
        size_t start;
        size_t len;
        if (strncmp(line, "R110_MANIFEST 1", 15) == 0) saw_header = 1;
        if (strncmp(trim_ascii(line), "case ", 5) != 0) continue;
        assert(field_value(line, "input", input, sizeof(input)));
        assert(field_value(line, "rule110_initial", initial, sizeof(initial)));
        assert(field_value(line, "steps", steps, sizeof(steps)));
        assert(field_value(line, "payload_start", start_text, sizeof(start_text)));
        assert(field_value(line, "payload_len", len_text, sizeof(len_text)));
        assert(field_value(line, "expected_payload", expected, sizeof(expected)));
        start = (size_t)strtoul(start_text, NULL, 10);
        len = (size_t)strtoul(len_text, NULL, 10);
        assert(strcmp(steps, "0") == 0);
        assert(strcmp(input, expected) == 0);
        assert(strlen(input) == len);
        assert(start + len <= strlen(initial));
        assert(strncmp(initial + start, expected, len) == 0);
        cases++;
    }
    fclose(f);
    assert(saw_header);
    assert(cases == expected_cases);
}

static int bits_to_bytes(const char *input, uint8_t **out, size_t *out_len) {
    size_t len = strlen(input);
    uint8_t *bytes = (uint8_t *)malloc(len ? len : 1);
    if (bytes == NULL) return 0;
    for (size_t i = 0; i < len; i++) bytes[i] = (uint8_t)(input[i] == '1');
    *out = bytes;
    *out_len = len;
    return 1;
}

static void free_bhist(BHist *h) {
    free(h->choices);
    h->choices = NULL;
    h->depth = 0;
}

static int bhist_equal(const BHist *a, const BHist *b) {
    return a->depth == b->depth &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
}

static int bhist_all_e0(const BHist *h) {
    for (size_t i = 0; i < h->depth; i++) {
        if (h->choices[i] != 0) return 0;
    }
    return 1;
}

static int decode_one_bhist_exact(const char *input, BHist *out) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    GcBhistDecResult r;
    assert(bits_to_bytes(input, &bytes, &len));
    r = gc_bhist_decode(bytes, len, 8192);
    free(bytes);
    if (r.status != GC_OK || r.bytes_consumed != len) {
        free_bhist(&r.bhist);
        return 0;
    }
    *out = r.bhist;
    return 1;
}

static int decode_two_bhist_exact(const char *input, BHist *a, BHist *b) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off;
    GcBhistDecResult r1;
    GcBhistDecResult r2;
    assert(bits_to_bytes(input, &bytes, &len));
    r1 = gc_bhist_decode(bytes, len, 8192);
    assert(r1.status == GC_OK);
    off = r1.bytes_consumed;
    r2 = gc_bhist_decode(bytes + off, len - off, 8192);
    free(bytes);
    assert(r2.status == GC_OK);
    assert(off + r2.bytes_consumed == len);
    *a = r1.bhist;
    *b = r2.bhist;
    return 1;
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

static void free_event(GcDecResult *r) {
    free(r->event);
    r->event = NULL;
    r->event_len = 0;
}

static void audit_nat_len(const AuditManifest *m) {
    for (size_t i = 0; i < m->count; i++) {
        BHist h;
        char value[64];
        assert(decode_one_bhist_exact(m->cases[i].input, &h));
        if (field_value(m->cases[i].line, "nat", value, sizeof(value))) {
            assert(h.depth == (size_t)strtoul(value, NULL, 10));
        }
        assert(field_value(m->cases[i].line, "all_e0", value, sizeof(value)));
        assert(bhist_all_e0(&h) == (strcmp(value, "yes") == 0));
        assert(field_value(m->cases[i].line, "bhist_len", value, sizeof(value)));
        assert(h.depth == (size_t)strtoul(value, NULL, 10));
        free_bhist(&h);
    }
}

static void audit_term_embedding(const AuditManifest *m) {
    for (size_t i = 0; i < m->count; i++) {
        char value[64];
        if (field_value(m->cases[i].line, "closed_at_0", value, sizeof(value))) {
            BHist h;
            assert(decode_one_bhist_exact(m->cases[i].input, &h));
            assert(payload_closed_at_choices(h.choices, h.depth, 3));
            free_bhist(&h);
        } else {
            BHist a;
            BHist b;
            int eq;
            assert(decode_two_bhist_exact(m->cases[i].input, &a, &b));
            eq = bhist_equal(&a, &b);
            assert(field_value(m->cases[i].line, "term_equal", value, sizeof(value)));
            assert(eq == (strcmp(value, "yes") == 0));
            assert(field_value(m->cases[i].line, "hist_equal", value, sizeof(value)));
            assert(eq == (strcmp(value, "yes") == 0));
            free_bhist(&a);
            free_bhist(&b);
        }
    }
}

static void audit_atom_infer(const AuditManifest *m) {
    for (size_t i = 0; i < m->count; i++) {
        uint8_t *bytes = NULL;
        size_t len = 0;
        size_t off;
        GcDecResult ctx;
        GcDecResult atom;
        char value[64];
        int some_sort = 0;
        assert(bits_to_bytes(m->cases[i].input, &bytes, &len));
        ctx = gc_dec_event(bytes, len, 8192);
        assert(ctx.status == GC_OK);
        for (size_t j = 0; j < ctx.event_len; j++) assert(ctx.event[j] == 0);
        off = ctx.bytes_consumed;
        atom = gc_dec_event(bytes + off, len - off, 8192);
        assert(atom.status == GC_OK);
        assert(off + atom.bytes_consumed == len);
        if (atom.event_len == 1 && atom.event[0] == 0) {
            some_sort = 1;
        } else if (atom.event_len >= 1 && atom.event[0] == 1) {
            int valid_var = 1;
            for (size_t j = 1; j < atom.event_len; j++) {
                if (atom.event[j] != 0) valid_var = 0;
            }
            some_sort = valid_var && atom.event_len - 1 < ctx.event_len;
        }
        assert(field_value(m->cases[i].line, "infer", value, sizeof(value)));
        assert(some_sort == (strcmp(value, "some_sort") == 0));
        free_event(&ctx);
        free_event(&atom);
        free(bytes);
    }
}

static void audit_manifest_triplet(const char *enum_path, const char *r110_path,
                                   const char *tmp_path,
                                   void (*body)(const AuditManifest *)) {
    AuditManifest m;
    assert(parse_manifest(enum_path, &m));
    assert_generate_idempotent(enum_path, r110_path, tmp_path);
    assert_r110_payloads(r110_path, m.count);
    body(&m);
}

int main(void) {
    printf("== test_meta_cic_audit ==\n");
    audit_manifest_triplet("manifests/meta_cic/bhist_nat_len.enum.ct",
                           "manifests/meta_cic/bhist_nat_len.r110.ct",
                           "tests/.bhist_nat_len.audit.r110.ct",
                           audit_nat_len);
    printf("  bhist_nat_len audit: 5/5 cases PASS\n");
    audit_manifest_triplet("manifests/meta_cic/bhist_term_embedding.enum.ct",
                           "manifests/meta_cic/bhist_term_embedding.r110.ct",
                           "tests/.bhist_term_embedding.audit.r110.ct",
                           audit_term_embedding);
    printf("  bhist_term_embedding audit: 8/8 cases PASS\n");
    audit_manifest_triplet("manifests/meta_cic/atom_infer.enum.ct",
                           "manifests/meta_cic/atom_infer.r110.ct",
                           "tests/.atom_infer.audit.r110.ct",
                           audit_atom_infer);
    printf("  atom_infer audit: 7/7 cases PASS\n");
    printf("ALL test_meta_cic_audit assertions passed\n");
    return 0;
}
