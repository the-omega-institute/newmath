#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <ctype.h>

#define MAX_CASES 16
#define MAX_LINE 4096
#define MAX_TEXT 2048
#define FOLD_FIELD_COUNT 9

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
    uint8_t *fields[FOLD_FIELD_COUNT];
    size_t lens[FOLD_FIELD_COUNT];
} FoldFlow;

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
            if (out->count >= MAX_CASES) {
                fclose(f);
                return 0;
            }
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

static void free_event(GcDecResult *r) {
    free(r->event);
    r->event = NULL;
    r->event_len = 0;
}

static void fold_flow_free(FoldFlow *flow) {
    for (size_t i = 0; i < FOLD_FIELD_COUNT; i++) {
        free(flow->fields[i]);
        flow->fields[i] = NULL;
        flow->lens[i] = 0;
    }
}

static int event_is_tag(const GcDecResult *r, size_t tag_index) {
    if (r->event_len != tag_index + 1) return 0;
    for (size_t i = 0; i < tag_index; i++) {
        if (r->event[i] != 1) return 0;
    }
    return r->event[tag_index] == 0;
}

static int decode_event(const uint8_t *bytes, size_t len, size_t *off,
                        GcDecResult *out) {
    *out = gc_dec_event(bytes + *off, len - *off, 8192);
    if (out->status != GC_OK) return 0;
    *off += out->bytes_consumed;
    return 1;
}

static int decode_fold_flow(const uint8_t *bytes, size_t len, size_t *off,
                            FoldFlow *flow) {
    memset(flow, 0, sizeof(*flow));
    for (size_t i = 0; i < FOLD_FIELD_COUNT; i++) {
        GcDecResult tag;
        GcDecResult field;
        if (!decode_event(bytes, len, off, &tag)) return 0;
        assert(event_is_tag(&tag, i));
        free_event(&tag);
        if (!decode_event(bytes, len, off, &field)) return 0;
        flow->fields[i] = field.event;
        flow->lens[i] = field.event_len;
    }
    return 1;
}

static int fold_fields_equal(const FoldFlow *a, const FoldFlow *b) {
    for (size_t i = 0; i < FOLD_FIELD_COUNT; i++) {
        if (a->lens[i] != b->lens[i]) return 0;
        if (a->lens[i] != 0 && memcmp(a->fields[i], b->fields[i], a->lens[i]) != 0) {
            return 0;
        }
    }
    return 1;
}

static void audit_single_flow_case(const AuditCase *c) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off = 0;
    FoldFlow flow;
    char value[64];
    assert(bits_to_bytes(c->input, &bytes, &len));
    assert(decode_fold_flow(bytes, len, &off, &flow));
    assert(off == len);
    if (field_value(c->line, "fields", value, sizeof(value))) {
        assert(strtoul(value, NULL, 10) == FOLD_FIELD_COUNT);
    }
    if (field_value(c->line, "events", value, sizeof(value))) {
        assert(strtoul(value, NULL, 10) == FOLD_FIELD_COUNT * 2);
    }
    if (field_value(c->line, "tag_layout", value, sizeof(value))) {
        assert(strcmp(value, "canonical") == 0);
    }
    fold_flow_free(&flow);
    free(bytes);
}

static void audit_injectivity_case(const AuditCase *c) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    size_t off = 0;
    FoldFlow left;
    FoldFlow right;
    char value[64];
    int fields_equal;
    assert(bits_to_bytes(c->input, &bytes, &len));
    assert(decode_fold_flow(bytes, len, &off, &left));
    assert(decode_fold_flow(bytes, len, &off, &right));
    assert(off == len);
    fields_equal = fold_fields_equal(&left, &right);
    assert(field_value(c->line, "fields_equal", value, sizeof(value)));
    assert(fields_equal == (strcmp(value, "yes") == 0));
    assert(field_value(c->line, "flows_equal", value, sizeof(value)));
    assert(fields_equal == (strcmp(value, "yes") == 0));
    fold_flow_free(&left);
    fold_flow_free(&right);
    free(bytes);
}

static void audit_single_flow_manifest(const AuditManifest *m) {
    for (size_t i = 0; i < m->count; i++) audit_single_flow_case(&m->cases[i]);
}

static void audit_injectivity_manifest(const AuditManifest *m) {
    for (size_t i = 0; i < m->count; i++) audit_injectivity_case(&m->cases[i]);
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
    printf("== test_fold_up_audit ==\n");
    audit_manifest_triplet("manifests/fold_up/fold_round_trip.enum.ct",
                           "manifests/fold_up/fold_round_trip.r110.ct",
                           "tests/.fold_round_trip.audit.r110.ct",
                           audit_single_flow_manifest);
    printf("  fold_round_trip audit: 3/3 cases PASS\n");
    audit_manifest_triplet("manifests/fold_up/fold_tag_layout.enum.ct",
                           "manifests/fold_up/fold_tag_layout.r110.ct",
                           "tests/.fold_tag_layout.audit.r110.ct",
                           audit_single_flow_manifest);
    printf("  fold_tag_layout audit: 3/3 cases PASS\n");
    audit_manifest_triplet("manifests/fold_up/fold_injectivity.enum.ct",
                           "manifests/fold_up/fold_injectivity.r110.ct",
                           "tests/.fold_injectivity.audit.r110.ct",
                           audit_injectivity_manifest);
    printf("  fold_injectivity audit: 3/3 cases PASS\n");
    printf("ALL test_fold_up_audit assertions passed\n");
    return 0;
}
