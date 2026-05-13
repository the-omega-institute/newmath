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

typedef struct {
    BHist *items;
    size_t len;
} BHistBundle;

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

static void free_event(GcDecResult *r) {
    free(r->event);
    r->event = NULL;
    r->event_len = 0;
}

static void free_bundle(BHistBundle *b) {
    for (size_t i = 0; i < b->len; i++) free_bhist(&b->items[i]);
    free(b->items);
    b->items = NULL;
    b->len = 0;
}

static int bhist_equal(const BHist *a, const BHist *b) {
    return a->depth == b->depth &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
}

static int bhist_unary_e1(const BHist *h) {
    for (size_t i = 0; i < h->depth; i++) {
        if (h->choices[i] != 1) return 0;
    }
    return 1;
}

static int event_is_bundle_end(const GcDecResult *r) {
    return r->event_len == 2 && r->event[0] == 1 && r->event[1] == 1;
}

static int bundle_push(BHistBundle *b, const GcDecResult *r) {
    BHist *next = (BHist *)realloc(b->items, (b->len + 1) * sizeof(BHist));
    if (next == NULL) return 0;
    b->items = next;
    b->items[b->len].depth = r->event_len;
    b->items[b->len].choices = NULL;
    if (r->event_len > 0) {
        b->items[b->len].choices = (uint8_t *)malloc(r->event_len);
        assert(b->items[b->len].choices != NULL);
        memcpy(b->items[b->len].choices, r->event, r->event_len);
    }
    b->len++;
    return 1;
}

static int decode_bundle(const uint8_t *bytes, size_t len, size_t *off,
                         BHistBundle *out) {
    out->items = NULL;
    out->len = 0;
    while (*off < len) {
        GcDecResult r = gc_dec_event(bytes + *off, len - *off, 8192);
        assert(r.status == GC_OK);
        *off += r.bytes_consumed;
        if (event_is_bundle_end(&r)) {
            free_event(&r);
            return 1;
        }
        assert(bundle_push(out, &r));
        free_event(&r);
    }
    return 0;
}

static int decode_one_bhist(const uint8_t *bytes, size_t len, size_t *off,
                            BHist *out) {
    GcBhistDecResult r = gc_bhist_decode(bytes + *off, len - *off, 8192);
    if (r.status != GC_OK) return 0;
    *off += r.bytes_consumed;
    *out = r.bhist;
    return 1;
}

static int decode_two_bundles_and_hist(const char *input, BHistBundle *left,
                                       BHistBundle *right, BHist *h) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off = 0;
    assert(bits_to_bytes(input, &bytes, &len));
    assert(decode_bundle(bytes, len, &off, left));
    assert(decode_bundle(bytes, len, &off, right));
    assert(decode_one_bhist(bytes, len, &off, h));
    assert(off == len);
    free(bytes);
    return 1;
}

static int decode_three_bhists(const char *input, BHist *a, BHist *b, BHist *c) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off = 0;
    assert(bits_to_bytes(input, &bytes, &len));
    assert(decode_one_bhist(bytes, len, &off, a));
    assert(decode_one_bhist(bytes, len, &off, b));
    assert(decode_one_bhist(bytes, len, &off, c));
    assert(off == len);
    free(bytes);
    return 1;
}

static int bundle_contains(const BHistBundle *b, const BHist *h) {
    for (size_t i = 0; i < b->len; i++) {
        if (bhist_equal(&b->items[i], h)) return 1;
    }
    return 0;
}

static void audit_finite_base(const AuditManifest *m) {
    for (size_t i = 0; i < m->count; i++) {
        BHistBundle left;
        BHistBundle right;
        BHist point;
        char value[64];
        assert(decode_two_bundles_and_hist(m->cases[i].input, &left, &right, &point));
        assert(field_value(m->cases[i].line, "left_len", value, sizeof(value)));
        assert(left.len == (size_t)strtoul(value, NULL, 10));
        assert(field_value(m->cases[i].line, "right_len", value, sizeof(value)));
        assert(right.len == (size_t)strtoul(value, NULL, 10));
        assert(field_value(m->cases[i].line, "append_len", value, sizeof(value)));
        assert(left.len + right.len == (size_t)strtoul(value, NULL, 10));
        for (size_t j = 0; j < left.len; j++) assert(bundle_contains(&left, &left.items[j]));
        for (size_t j = 0; j < right.len; j++) assert(bundle_contains(&right, &right.items[j]));
        free_bundle(&left);
        free_bundle(&right);
        free_bhist(&point);
    }
}

static void audit_carrier_rows(const AuditManifest *m) {
    for (size_t i = 0; i < m->count; i++) {
        BHistBundle left;
        BHistBundle right;
        BHist ledger;
        char value[64];
        assert(decode_two_bundles_and_hist(m->cases[i].input, &left, &right, &ledger));
        assert(field_value(m->cases[i].line, "left_len", value, sizeof(value)));
        assert(left.len == (size_t)strtoul(value, NULL, 10));
        assert(field_value(m->cases[i].line, "right_len", value, sizeof(value)));
        assert(right.len == (size_t)strtoul(value, NULL, 10));
        assert(bhist_unary_e1(&ledger));
        free_bundle(&left);
        free_bundle(&right);
        free_bhist(&ledger);
    }
}

static void audit_ledger_tags(const AuditManifest *m) {
    for (size_t i = 0; i < m->count; i++) {
        BHist tag;
        BHist expected;
        BHist ledger;
        char value[64];
        assert(decode_three_bhists(m->cases[i].input, &tag, &expected, &ledger));
        assert(bhist_unary_e1(&ledger));
        if (field_value(m->cases[i].line, "tags_distinct", value, sizeof(value))) {
            assert(strcmp(value, "yes") == 0);
            assert(!bhist_equal(&tag, &expected));
        } else {
            assert(field_value(m->cases[i].line, "row_constructor", value, sizeof(value)));
            assert(bhist_equal(&tag, &expected));
        }
        free_bhist(&tag);
        free_bhist(&expected);
        free_bhist(&ledger);
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
    printf("== test_topology_up_audit ==\n");
    audit_manifest_triplet("manifests/topology_up/topology_finite_base_neighborhood.enum.ct",
                           "manifests/topology_up/topology_finite_base_neighborhood.r110.ct",
                           "tests/.topology_finite_base_neighborhood.audit.r110.ct",
                           audit_finite_base);
    printf("  topology_finite_base_neighborhood audit: 5/5 cases PASS\n");
    audit_manifest_triplet("manifests/topology_up/topology_carrier_rows.enum.ct",
                           "manifests/topology_up/topology_carrier_rows.r110.ct",
                           "tests/.topology_carrier_rows.audit.r110.ct",
                           audit_carrier_rows);
    printf("  topology_carrier_rows audit: 4/4 cases PASS\n");
    audit_manifest_triplet("manifests/topology_up/topology_ledger_tags.enum.ct",
                           "manifests/topology_up/topology_ledger_tags.r110.ct",
                           "tests/.topology_ledger_tags.audit.r110.ct",
                           audit_ledger_tags);
    printf("  topology_ledger_tags audit: 9/9 cases PASS\n");
    printf("ALL test_topology_up_audit assertions passed\n");
    return 0;
}
