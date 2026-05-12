#include "groundcompiler_encoding.h"
#include "rule110.h"

#include <assert.h>
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define R110_MANIFEST_PATH "manifests/mark/msame_refl.r110.ct"
#define CT_MANIFEST_PATH "manifests/mark/msame_refl.enum.ct"

typedef struct {
    char name[64];
    char input[256];
    uint8_t *initial;
    size_t initial_len;
    size_t steps;
    size_t payload_start;
    size_t payload_len;
    char expected_payload[256];
    int expected_reflexive;
} R110Case;

typedef struct {
    size_t initial_length;
    size_t assertion_count;
    R110Case cases[16];
    size_t case_count;
} R110Manifest;

static char *trim_ascii(char *s) {
    char *end;

    while (*s && isspace((unsigned char)*s)) s++;
    end = s + strlen(s);
    while (end > s && isspace((unsigned char)end[-1])) end--;
    *end = '\0';
    return s;
}

static int parse_size_value(const char *s, size_t *out) {
    char *end = NULL;
    unsigned long value;

    value = strtoul(s, &end, 10);
    if (end == s) return 0;
    while (*end && isspace((unsigned char)*end)) end++;
    if (*end != '\0') return 0;
    *out = (size_t)value;
    return 1;
}

static int copy_text_value(char *dst, size_t dst_cap, const char *src) {
    size_t len = strlen(src);

    if (len + 1 > dst_cap) return 0;
    memcpy(dst, src, len + 1);
    return 1;
}

static int bit_string_to_cells(const char *bits,
                               size_t expected_len,
                               uint8_t **out) {
    uint8_t *cells;
    size_t len = strlen(bits);

    if (len != expected_len) return 0;
    cells = (uint8_t *)malloc(expected_len ? expected_len : 1);
    if (cells == NULL) return 0;

    for (size_t i = 0; i < expected_len; i++) {
        if (bits[i] != '0' && bits[i] != '1') {
            free(cells);
            return 0;
        }
        cells[i] = (uint8_t)(bits[i] == '1');
    }

    *out = cells;
    return 1;
}

static int parse_key_value(R110Case *c,
                           const char *key,
                           const char *value,
                           size_t manifest_initial_len) {
    if (strcmp(key, "input") == 0) {
        return copy_text_value(c->input, sizeof(c->input), value);
    }
    if (strcmp(key, "rule110_initial") == 0) {
        return bit_string_to_cells(value, manifest_initial_len, &c->initial);
    }
    if (strcmp(key, "steps") == 0) {
        return parse_size_value(value, &c->steps);
    }
    if (strcmp(key, "payload_start") == 0) {
        return parse_size_value(value, &c->payload_start);
    }
    if (strcmp(key, "payload_len") == 0) {
        return parse_size_value(value, &c->payload_len);
    }
    if (strcmp(key, "expected_payload") == 0) {
        return copy_text_value(c->expected_payload,
                               sizeof(c->expected_payload),
                               value);
    }
    if (strcmp(key, "expected_reflexive") == 0) {
        c->expected_reflexive = (strcmp(value, "yes") == 0);
        return c->expected_reflexive;
    }
    if (strcmp(key, "encoding") == 0) {
        return strcmp(value, "groundcompiler_event_pair") == 0;
    }
    if (strcmp(key, "construction") == 0) {
        return strcmp(value, "one_step_preimage") == 0;
    }
    return 0;
}

static int parse_case_line(char *line,
                           size_t manifest_initial_len,
                           R110Case *out) {
    char *cursor;
    char *colon;
    char *field;

    memset(out, 0, sizeof(*out));
    out->expected_reflexive = 0;

    if (strncmp(line, "case ", 5) != 0) return 0;
    cursor = line + 5;
    colon = strchr(cursor, ':');
    if (colon == NULL) return 0;
    *colon = '\0';
    if (!copy_text_value(out->name, sizeof(out->name), trim_ascii(cursor))) {
        return 0;
    }
    cursor = colon + 1;

    field = strtok(cursor, ";");
    while (field != NULL) {
        char *eq;
        char *key;
        char *value;

        field = trim_ascii(field);
        eq = strchr(field, '=');
        if (eq == NULL) return 0;
        *eq = '\0';
        key = trim_ascii(field);
        value = trim_ascii(eq + 1);
        if (!parse_key_value(out, key, value, manifest_initial_len)) {
            return 0;
        }
        field = strtok(NULL, ";");
    }

    out->initial_len = manifest_initial_len;
    if (out->initial == NULL || out->input[0] == '\0' ||
        out->expected_payload[0] == '\0') {
        return 0;
    }
    if (out->payload_start > out->initial_len ||
        out->payload_len > out->initial_len - out->payload_start) {
        return 0;
    }
    if (strlen(out->expected_payload) != out->payload_len) return 0;

    return 1;
}

static void free_manifest(R110Manifest *m) {
    for (size_t i = 0; i < m->case_count; i++) {
        free(m->cases[i].initial);
        m->cases[i].initial = NULL;
    }
}

static int load_r110_manifest(const char *path, R110Manifest *out) {
    FILE *f = fopen(path, "r");
    char line_buf[2048];
    int saw_version = 0;
    int saw_source = 0;
    int saw_construction = 0;

    if (f == NULL) return 0;
    memset(out, 0, sizeof(*out));

    while (fgets(line_buf, sizeof(line_buf), f) != NULL) {
        char *line = trim_ascii(line_buf);

        if (line[0] == '\0' || line[0] == '#') continue;
        if (strcmp(line, "R110_MANIFEST 1") == 0) {
            saw_version = 1;
        } else if (strcmp(line,
                          "SOURCE_CT rule110/manifests/mark/msame_refl.enum.ct") == 0) {
            saw_source = 1;
        } else if (strcmp(line, "CONSTRUCTION one_step_preimage") == 0) {
            saw_construction = 1;
        } else if (strncmp(line, "INITIAL_LENGTH ", 15) == 0) {
            if (!parse_size_value(line + 15, &out->initial_length)) {
                fclose(f);
                return 0;
            }
        } else if (strncmp(line, "ASSERTIONS ", 11) == 0) {
            if (!parse_size_value(line + 11, &out->assertion_count)) {
                fclose(f);
                return 0;
            }
        } else if (strncmp(line, "case ", 5) == 0) {
            if (out->case_count >= sizeof(out->cases) / sizeof(out->cases[0])) {
                fclose(f);
                free_manifest(out);
                return 0;
            }
            if (!parse_case_line(line,
                                 out->initial_length,
                                 &out->cases[out->case_count])) {
                fclose(f);
                free_manifest(out);
                return 0;
            }
            out->case_count++;
        } else {
            fclose(f);
            free_manifest(out);
            return 0;
        }
    }

    fclose(f);
    if (!saw_version || !saw_source || !saw_construction ||
        out->initial_length == 0 ||
        out->assertion_count != out->case_count) {
        free_manifest(out);
        return 0;
    }
    return 1;
}

static int payload_matches(const uint8_t *cells, const R110Case *c) {
    for (size_t i = 0; i < c->payload_len; i++) {
        char got = cells[c->payload_start + i] ? '1' : '0';
        if (got != c->expected_payload[i]) return 0;
    }
    return 1;
}

static int decode_expected_reflexive_payload(const R110Case *c) {
    uint8_t payload[256];
    GcDecResult first;
    GcDecResult second;
    size_t consumed;
    int equal;

    if (c->payload_len > sizeof(payload)) return 0;
    for (size_t i = 0; i < c->payload_len; i++) {
        payload[i] = (uint8_t)(c->expected_payload[i] == '1');
    }

    first = gc_dec_event(payload, c->payload_len, 64);
    if (first.status != GC_OK) {
        free(first.event);
        return 0;
    }
    consumed = first.bytes_consumed;

    second = gc_dec_event(payload + consumed, c->payload_len - consumed, 64);
    if (second.status != GC_OK) {
        free(first.event);
        free(second.event);
        return 0;
    }
    consumed += second.bytes_consumed;
    if (consumed != c->payload_len) {
        free(first.event);
        free(second.event);
        return 0;
    }

    equal = first.event_len == second.event_len &&
            memcmp(first.event, second.event, first.event_len) == 0;
    free(first.event);
    free(second.event);
    return equal;
}

static void verify_ct_manifest_is_empty_program(void) {
    FILE *f = fopen(CT_MANIFEST_PATH, "r");
    char line_buf[256];
    int saw_productions_zero = 0;

    assert(f != NULL);
    while (fgets(line_buf, sizeof(line_buf), f) != NULL) {
        char *line = trim_ascii(line_buf);
        if (strcmp(line, "PRODUCTIONS 0") == 0) {
            saw_productions_zero = 1;
            break;
        }
    }
    fclose(f);
    assert(saw_productions_zero);
}

static void verify_case(const R110Case *c) {
    uint8_t *cells = (uint8_t *)malloc(c->initial_len ? c->initial_len : 1);

    assert(cells != NULL);
    memcpy(cells, c->initial, c->initial_len);
    r110_run_n_steps(cells, c->initial_len, c->steps);

    assert(payload_matches(cells, c));
    assert(strcmp(c->input, c->expected_payload) == 0);
    assert(c->expected_reflexive);
    assert(decode_expected_reflexive_payload(c));

    free(cells);
    printf("  %s: Rule 110 payload round-trip PASS\n", c->name);
}

int main(void) {
    R110Manifest manifest;

    printf("== test_r110_round_trip ==\n");
    verify_ct_manifest_is_empty_program();
    assert(load_r110_manifest(R110_MANIFEST_PATH, &manifest));
    assert(manifest.case_count == 2);
    for (size_t i = 0; i < manifest.case_count; i++) {
        verify_case(&manifest.cases[i]);
    }
    free_manifest(&manifest);
    printf("ALL test_r110_round_trip tests passed\n");
    return 0;
}
