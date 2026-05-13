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
    BHist items[5];
} BHistSeq5;

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
            char input[MAX_TEXT];
            if (out->count >= MAX_CASES) {
                fclose(f);
                return 0;
            }
            colon = strchr(s + 5, ':');
            if (colon == NULL) {
                fclose(f);
                return 0;
            }
            *colon = '\0';
            if (strlen(trim_ascii(s + 5)) >= sizeof(out->cases[out->count].name)) {
                fclose(f);
                return 0;
            }
            strcpy(out->cases[out->count].name, trim_ascii(s + 5));
            if (!field_value(raw, "input", input, sizeof(input))) {
                fclose(f);
                return 0;
            }
            for (size_t i = 0; input[i] != '\0'; i++) {
                if (input[i] != '0' && input[i] != '1') {
                    fclose(f);
                    return 0;
                }
            }
            strcpy(out->cases[out->count].input, input);
            if (strlen(raw) >= sizeof(out->cases[out->count].line)) {
                fclose(f);
                return 0;
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

    if (fa == NULL || fb == NULL) {
        if (fa != NULL) fclose(fa);
        if (fb != NULL) fclose(fb);
        return 0;
    }
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
    int rc;
    assert(snprintf(command, sizeof(command), "./encoder/generate_r110 %s %s > /dev/null",
                    enum_path, tmp_path) < (int)sizeof(command));
    rc = system(command);
    assert(rc == 0);
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

static int bhist_empty(const BHist *h) {
    return h->depth == 0;
}

static int bhist_unary_e1(const BHist *h) {
    for (size_t i = 0; i < h->depth; i++) {
        if (h->choices[i] != 1) return 0;
    }
    return 1;
}

static int decode_bhists(const char *input, BHistSeq5 *seq, size_t count) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off = 0;

    if (!bits_to_bytes(input, &bytes, &len)) return 0;
    for (size_t i = 0; i < count; i++) {
        GcBhistDecResult r = gc_bhist_decode(bytes + off, len - off, 8192);
        if (r.status != GC_OK) {
            free(bytes);
            return 0;
        }
        seq->items[i] = r.bhist;
        off += r.bytes_consumed;
    }
    free(bytes);
    return off == len;
}

static void free_seq(BHistSeq5 *seq, size_t count) {
    for (size_t i = 0; i < count; i++) free_bhist(&seq->items[i]);
}

static BHist bhist_append_value(const BHist *left, const BHist *right) {
    BHist out;
    out.depth = left->depth + right->depth;
    out.choices = NULL;
    if (out.depth == 0) return out;
    out.choices = (uint8_t *)malloc(out.depth);
    assert(out.choices != NULL);
    if (right->depth > 0) memcpy(out.choices, right->choices, right->depth);
    if (left->depth > 0) memcpy(out.choices + right->depth, left->choices, left->depth);
    return out;
}

static void audit_modn_rows(const AuditManifest *m) {
    for (size_t i = 0; i < m->count; i++) {
        BHistSeq5 seq;
        char value[64];
        assert(field_value(m->cases[i].line, "theorem", value, sizeof(value)));
        assert(decode_bhists(m->cases[i].input, &seq, 4));
        assert(bhist_unary_e1(&seq.items[0]));
        assert(bhist_empty(&seq.items[3]));
        if (field_value(m->cases[i].line, "carrier_premise", value, sizeof(value))) {
            assert((bhist_empty(&seq.items[1]) ? 1 : 0) == (strcmp(value, "true") == 0));
        }
        if (field_value(m->cases[i].line, "classifier_premise", value, sizeof(value))) {
            int premise = bhist_empty(&seq.items[1]) &&
                          bhist_empty(&seq.items[2]) &&
                          bhist_equal(&seq.items[1], &seq.items[2]);
            assert(premise == (strcmp(value, "true") == 0));
        }
        free_seq(&seq, 4);
    }
}

static void audit_modn_operations(const AuditManifest *m) {
    for (size_t i = 0; i < m->count; i++) {
        BHistSeq5 seq;
        char value[64];
        int carrier;
        assert(decode_bhists(m->cases[i].input, &seq, 5));
        assert(bhist_unary_e1(&seq.items[0]));
        assert(bhist_empty(&seq.items[3]));
        assert(bhist_empty(&seq.items[4]));
        assert(field_value(m->cases[i].line, "carrier_premise", value, sizeof(value)));
        carrier = bhist_empty(&seq.items[1]) && bhist_empty(&seq.items[2]);
        assert(carrier == (strcmp(value, "true") == 0));
        free_seq(&seq, 5);
    }
}

static void audit_s1_rows(const AuditManifest *m) {
    for (size_t i = 0; i < m->count; i++) {
        BHistSeq5 seq;
        BHist dy;
        BHist expected_tail;
        assert(decode_bhists(m->cases[i].input, &seq, 5));
        assert(seq.items[0].depth > 0 && seq.items[0].choices[0] == 1);
        assert(seq.items[1].depth > 0 && seq.items[1].choices[0] == 1);
        assert(seq.items[2].depth == 2 && seq.items[2].choices[0] == 1 &&
               seq.items[2].choices[1] == 1);
        assert(seq.items[3].depth > 0 && seq.items[3].choices[0] == 1);
        assert(seq.items[3].depth == seq.items[4].depth + 1);
        assert(memcmp(seq.items[3].choices + 1, seq.items[4].choices,
                      seq.items[4].depth) == 0);
        dy.choices = seq.items[1].choices + 1;
        dy.depth = seq.items[1].depth - 1;
        expected_tail = bhist_append_value(&seq.items[0], &dy);
        assert(bhist_equal(&seq.items[4], &expected_tail));
        free_bhist(&expected_tail);
        free_seq(&seq, 5);
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
    printf("== test_circle_up_audit ==\n");
    audit_manifest_triplet("manifests/circle_up/circle_modn_rows.enum.ct",
                           "manifests/circle_up/circle_modn_rows.r110.ct",
                           "tests/.circle_modn_rows.audit.r110.ct",
                           audit_modn_rows);
    printf("  circle_modn_rows audit: 4/4 cases PASS\n");
    audit_manifest_triplet("manifests/circle_up/circle_modn_operations.enum.ct",
                           "manifests/circle_up/circle_modn_operations.r110.ct",
                           "tests/.circle_modn_operations.audit.r110.ct",
                           audit_modn_operations);
    printf("  circle_modn_operations audit: 4/4 cases PASS\n");
    audit_manifest_triplet("manifests/circle_up/circle_s1_rows.enum.ct",
                           "manifests/circle_up/circle_s1_rows.r110.ct",
                           "tests/.circle_s1_rows.audit.r110.ct",
                           audit_s1_rows);
    printf("  circle_s1_rows audit: 4/4 cases PASS\n");
    printf("ALL test_circle_up_audit assertions passed\n");
    return 0;
}
