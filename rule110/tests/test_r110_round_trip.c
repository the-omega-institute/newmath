#include "rule110.h"

#include <assert.h>
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_R110_CASES 512
#define MAX_CT_CASES 512
#define MAX_NAME 128
#define MAX_BITS 2048
#define MAX_PATH 512

typedef struct {
    char name[MAX_NAME];
    char input[MAX_BITS];
    uint8_t *initial;
    size_t initial_len;
    size_t steps;
    size_t payload_start;
    size_t payload_len;
    char expected_payload[MAX_BITS];
} R110Case;

typedef struct {
    char source_ct[MAX_PATH];
    size_t initial_length;
    size_t assertion_count;
    R110Case cases[MAX_R110_CASES];
    size_t case_count;
} R110Manifest;

typedef struct {
    char name[MAX_NAME];
    char input[MAX_BITS];
    int has_input;
    int binary_direct;
} CtCase;

typedef struct {
    size_t productions;
    size_t assertion_count;
    CtCase cases[MAX_CT_CASES];
    size_t case_count;
} CtManifest;

static const char *R110_MANIFESTS[] = {
    "manifests/ask/ask_basic.r110.ct",
    "manifests/bundle/bundle_length.r110.ct",
    "manifests/bundle/bundle_membership.r110.ct",
    "manifests/cont/cont_basic.r110.ct",
    "manifests/ext/ext_step.r110.ct",
    "manifests/external_binary/external_binary_basic.r110.ct",
    "manifests/gap/gap_basic.r110.ct",
    "manifests/ground_compiler/bhist_injectivity.r110.ct",
    "manifests/ground_compiler/flow_round_trip.r110.ct",
    "manifests/ground_compiler/reject_reasons.r110.ct",
    "manifests/hist/hsame_constructor_distinct.r110.ct",
    "manifests/hist/hsame_empty_inversion.r110.ct",
    "manifests/hist/hsame_refl.r110.ct",
    "manifests/hist/hsame_symm.r110.ct",
    "manifests/hist/hsame_trans.r110.ct",
    "manifests/mark/msame_no_confusion.r110.ct",
    "manifests/mark/msame_refl.r110.ct",
    "manifests/mark/msame_symm.r110.ct",
    "manifests/mark/msame_trans.r110.ct",
    "manifests/name_cert/name_cert_basic.r110.ct",
    "manifests/package/package_basic.r110.ct",
    "manifests/settled/settled_basic.r110.ct",
    "manifests/sig/samesig_equiv.r110.ct",
    "manifests/sig/sigrel_basic.r110.ct",
    "manifests/unary/unary_basic.r110.ct",
};

static const char *ALGO_R110_MANIFESTS[] = {
    "manifests/ask/ask_basic.algo.r110.ct",
    "manifests/bundle/bundle_length.algo.r110.ct",
    "manifests/bundle/bundle_membership.algo.r110.ct",
    "manifests/cont/cont_basic.algo.r110.ct",
    "manifests/ext/ext_step.algo.r110.ct",
    "manifests/external_binary/external_binary_basic.algo.r110.ct",
    "manifests/gap/gap_basic.algo.r110.ct",
    "manifests/hist/hsame_constructor_distinct.algo.r110.ct",
    "manifests/hist/hsame_empty_inversion.algo.r110.ct",
    "manifests/hist/hsame_refl.algo.r110.ct",
    "manifests/hist/hsame_symm.algo.r110.ct",
    "manifests/hist/hsame_trans.algo.r110.ct",
    "manifests/mark/msame_no_confusion.algo.r110.ct",
    "manifests/mark/msame_refl.algo.r110.ct",
    "manifests/mark/msame_symm.algo.r110.ct",
    "manifests/mark/msame_trans.algo.r110.ct",
    "manifests/name_cert/name_cert_basic.algo.r110.ct",
    "manifests/package/package_basic.algo.r110.ct",
    "manifests/settled/settled_basic.algo.r110.ct",
    "manifests/sig/samesig_equiv.algo.r110.ct",
    "manifests/sig/sigrel_basic.algo.r110.ct",
    "manifests/unary/unary_basic.algo.r110.ct",
};

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

static int normalize_input(char *dst, size_t dst_cap, const char *value) {
    if (strcmp(value, "<empty>") == 0) {
        return copy_text_value(dst, dst_cap, "");
    }
    return copy_text_value(dst, dst_cap, value);
}

static int is_binary_string_or_empty(const char *s) {
    if (s == NULL) return 0;
    for (size_t i = 0; s[i] != '\0'; i++) {
        if (s[i] != '0' && s[i] != '1') return 0;
    }
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

static int read_line_dynamic(FILE *f, char **out) {
    size_t cap = 4096;
    size_t len = 0;
    int ch;
    char *buf = (char *)malloc(cap);

    if (buf == NULL) return -1;
    while ((ch = fgetc(f)) != EOF) {
        if (len + 1 >= cap) {
            size_t next_cap = cap * 2;
            char *next = (char *)realloc(buf, next_cap);

            if (next == NULL) {
                free(buf);
                return -1;
            }
            buf = next;
            cap = next_cap;
        }
        if (ch == '\n') break;
        buf[len++] = (char)ch;
    }
    if (ch == EOF && len == 0) {
        free(buf);
        return 0;
    }
    if (len > 0 && buf[len - 1] == '\r') len--;
    buf[len] = '\0';
    *out = buf;
    return 1;
}

static int read_content_line_dynamic(FILE *f, char **out) {
    for (;;) {
        int rc = read_line_dynamic(f, out);
        char *trimmed;

        if (rc <= 0) return rc;
        trimmed = trim_ascii(*out);
        if (trimmed[0] == '\0' || trimmed[0] == '#') {
            free(*out);
            *out = NULL;
            continue;
        }
        if (trimmed != *out) memmove(*out, trimmed, strlen(trimmed) + 1);
        return 1;
    }
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
    if (strcmp(key, "encoding") == 0) {
        return strcmp(value, "direct_bit_payload") == 0 ||
               strcmp(value, "groundcompiler_event_pair") == 0;
    }
    if (strcmp(key, "construction") == 0) {
        return strcmp(value, "direct_initial_payload") == 0 ||
               strcmp(value, "one_step_preimage") == 0;
    }
    return 0;
}

static int parse_r110_case_line(char *line,
                                size_t manifest_initial_len,
                                R110Case *out) {
    char *cursor;
    char *colon;
    char *field;

    memset(out, 0, sizeof(*out));

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
    if (out->initial == NULL) return 0;
    if (out->payload_start > out->initial_len ||
        out->payload_len > out->initial_len - out->payload_start) {
        return 0;
    }
    if (strlen(out->input) != out->payload_len) return 0;
    if (strlen(out->expected_payload) != out->payload_len) return 0;

    return 1;
}

static void free_r110_manifest(R110Manifest *m) {
    for (size_t i = 0; i < m->case_count; i++) {
        free(m->cases[i].initial);
        m->cases[i].initial = NULL;
    }
}

static int load_r110_manifest(const char *path, R110Manifest *out) {
    FILE *f = fopen(path, "r");
    char line_buf[4096];
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
        } else if (strncmp(line, "SOURCE_CT ", 10) == 0) {
            if (!copy_text_value(out->source_ct,
                                 sizeof(out->source_ct),
                                 line + 10)) {
                fclose(f);
                return 0;
            }
            saw_source = 1;
        } else if (strcmp(line, "CONSTRUCTION direct_initial_payload") == 0 ||
                   strcmp(line, "CONSTRUCTION one_step_preimage") == 0) {
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
            if (out->case_count >= MAX_R110_CASES) {
                fclose(f);
                free_r110_manifest(out);
                return 0;
            }
            if (!parse_r110_case_line(line,
                                      out->initial_length,
                                      &out->cases[out->case_count])) {
                fclose(f);
                free_r110_manifest(out);
                return 0;
            }
            out->case_count++;
        } else if (strncmp(line, "skip ", 5) == 0) {
            continue;
        } else {
            fclose(f);
            free_r110_manifest(out);
            return 0;
        }
    }

    fclose(f);
    if (!saw_version || !saw_source || !saw_construction ||
        out->initial_length == 0 ||
        out->assertion_count != out->case_count) {
        free_r110_manifest(out);
        return 0;
    }
    return 1;
}

static int parse_ct_case_line(char *line, CtCase *out) {
    char *cursor;
    char *colon;
    char *field;

    memset(out, 0, sizeof(*out));
    cursor = trim_ascii(line);
    if (strncmp(cursor, "case ", 5) != 0) return 0;
    cursor += 5;

    colon = strchr(cursor, ':');
    if (colon == NULL) return -1;
    *colon = '\0';
    if (!copy_text_value(out->name, sizeof(out->name), trim_ascii(cursor))) {
        return -1;
    }

    field = colon + 1;
    for (;;) {
        char *semi = strchr(field, ';');
        char *eq;
        char *key;
        char *value;

        if (semi != NULL) *semi = '\0';
        field = trim_ascii(field);
        if (*field != '\0') {
            eq = strchr(field, '=');
            if (eq == NULL) break;
            *eq = '\0';
            key = trim_ascii(field);
            value = trim_ascii(eq + 1);
            if (strcmp(key, "input") == 0) {
                if (!normalize_input(out->input, sizeof(out->input), value)) {
                    return -1;
                }
                out->has_input = 1;
            }
        }

        if (semi == NULL) break;
        field = semi + 1;
    }

    out->binary_direct = out->has_input && is_binary_string_or_empty(out->input);
    return 1;
}

static int load_ct_manifest(const char *path, CtManifest *out) {
    FILE *f = fopen(path, "r");
    char line_buf[4096];
    int saw_productions = 0;
    int saw_assertions = 0;

    if (f == NULL && strncmp(path, "rule110/", 8) == 0) {
        f = fopen(path + 8, "r");
    }
    if (f == NULL) return 0;
    memset(out, 0, sizeof(*out));

    while (fgets(line_buf, sizeof(line_buf), f) != NULL) {
        char *line = trim_ascii(line_buf);

        if (line[0] == '\0' || line[0] == '#') continue;
        if (strncmp(line, "PRODUCTIONS ", 12) == 0) {
            if (!parse_size_value(line + 12, &out->productions)) {
                fclose(f);
                return 0;
            }
            saw_productions = 1;
        } else if (strncmp(line, "ASSERTIONS ", 11) == 0) {
            if (!parse_size_value(line + 11, &out->assertion_count)) {
                fclose(f);
                return 0;
            }
            saw_assertions = 1;
        } else if (strncmp(line, "case ", 5) == 0) {
            int rc;

            if (out->case_count >= MAX_CT_CASES) {
                fclose(f);
                return 0;
            }
            rc = parse_ct_case_line(line, &out->cases[out->case_count]);
            if (rc <= 0) {
                fclose(f);
                return 0;
            }
            out->case_count++;
        }
    }

    fclose(f);
    return saw_productions && saw_assertions && out->productions == 0 &&
           out->assertion_count == out->case_count;
}

static const CtCase *find_ct_case(const CtManifest *m, const char *name) {
    for (size_t i = 0; i < m->case_count; i++) {
        if (strcmp(m->cases[i].name, name) == 0) return &m->cases[i];
    }
    return NULL;
}

static size_t ct_binary_direct_count(const CtManifest *m) {
    size_t count = 0;

    for (size_t i = 0; i < m->case_count; i++) {
        if (m->cases[i].binary_direct) count++;
    }
    return count;
}

static int payload_matches(const uint8_t *cells, const R110Case *c) {
    for (size_t i = 0; i < c->payload_len; i++) {
        char got = cells[c->payload_start + i] ? '1' : '0';
        if (got != c->expected_payload[i]) return 0;
    }
    return 1;
}

static void verify_case(const R110Case *c, const CtManifest *ct) {
    const CtCase *source = find_ct_case(ct, c->name);
    uint8_t *cells = (uint8_t *)malloc(c->initial_len ? c->initial_len : 1);

    assert(source != NULL);
    assert(source->binary_direct);
    assert(strcmp(source->input, c->input) == 0);
    assert(strcmp(c->input, c->expected_payload) == 0);
    assert(cells != NULL);

    memcpy(cells, c->initial, c->initial_len);
    r110_run_n_steps(cells, c->initial_len, c->steps);
    assert(payload_matches(cells, c));

    free(cells);
}

static void verify_manifest(const char *path) {
    R110Manifest r110;
    CtManifest ct;
    size_t direct_count;

    assert(load_r110_manifest(path, &r110));
    assert(load_ct_manifest(r110.source_ct, &ct));

    direct_count = ct_binary_direct_count(&ct);
    assert(r110.case_count == direct_count);

    for (size_t i = 0; i < r110.case_count; i++) {
        verify_case(&r110.cases[i], &ct);
    }

    printf("  %s: %zu direct-carrier case(s) PASS\n",
           path,
           r110.case_count);
    free_r110_manifest(&r110);
}

static int parse_prefixed_size_line(const char *line,
                                    const char *prefix,
                                    size_t *out) {
    size_t prefix_len = strlen(prefix);

    if (strncmp(line, prefix, prefix_len) != 0) return 0;
    return parse_size_value(line + prefix_len, out);
}

static int read_exact_bit_payload(FILE *f,
                                  size_t expected_len,
                                  uint8_t **out) {
    char *line = NULL;
    int rc = read_content_line_dynamic(f, &line);

    if (rc != 1) return 0;
    if (!bit_string_to_cells(line, expected_len, out)) {
        free(line);
        return 0;
    }
    free(line);
    return 1;
}

static void verify_algo_case(FILE *f, const char *case_line, size_t steps) {
    char *line = NULL;
    uint8_t *initial = NULL;
    uint8_t *expected = NULL;
    uint8_t *cells = NULL;
    size_t initial_len = 0;
    size_t expected_len = 0;
    size_t ignored_len = 0;
    size_t ignored_steps = 0;
    int rc;

    assert(strncmp(case_line, "case ", 5) == 0);

    rc = read_content_line_dynamic(f, &line);
    assert(rc == 1 && strncmp(line, "INPUT ", 6) == 0);
    free(line);
    line = NULL;

    rc = read_content_line_dynamic(f, &line);
    assert(rc == 1 && parse_prefixed_size_line(line, "CT_STEPS ", &ignored_steps));
    free(line);
    line = NULL;

    rc = read_content_line_dynamic(f, &line);
    assert(rc == 1 && parse_prefixed_size_line(line, "CT_FINAL ", &ignored_len));
    free(line);
    line = NULL;

    if (ignored_len > 0) {
        uint8_t *ignored = NULL;

        assert(read_exact_bit_payload(f, ignored_len, &ignored));
        free(ignored);
    }

    rc = read_content_line_dynamic(f, &line);
    assert(rc == 1 && parse_prefixed_size_line(line,
                                               "RULE110_INITIAL ",
                                               &initial_len));
    free(line);
    line = NULL;
    assert(read_exact_bit_payload(f, initial_len, &initial));

    rc = read_content_line_dynamic(f, &line);
    assert(rc == 1 && parse_prefixed_size_line(line,
                                               "RULE110_FINAL ",
                                               &expected_len));
    free(line);
    line = NULL;
    assert(expected_len == initial_len);
    assert(read_exact_bit_payload(f, expected_len, &expected));

    cells = (uint8_t *)malloc(initial_len ? initial_len : 1);
    assert(cells != NULL);
    memcpy(cells, initial, initial_len);
    r110_run_n_steps(cells, initial_len, steps);
    for (size_t i = 0; i < expected_len; i++) {
        assert(cells[i] == expected[i]);
    }

    rc = read_content_line_dynamic(f, &line);
    assert(rc == 1 && strcmp(line, "ENDCASE") == 0);
    free(line);

    free(cells);
    free(initial);
    free(expected);
}

static void verify_algo_manifest(const char *path) {
    FILE *f = fopen(path, "r");
    char *line = NULL;
    size_t steps = 0;
    size_t assertions = 0;
    size_t seen = 0;
    int rc;

    assert(f != NULL);

    rc = read_content_line_dynamic(f, &line);
    assert(rc == 1 && strcmp(line, "ALGO_R110_MANIFEST 1") == 0);
    free(line);
    line = NULL;

    rc = read_content_line_dynamic(f, &line);
    assert(rc == 1 && strncmp(line, "SOURCE_CT ", 10) == 0);
    free(line);
    line = NULL;

    rc = read_content_line_dynamic(f, &line);
    assert(rc == 1 &&
           strcmp(line, "CONSTRUCTION cook_phase_exact_packet_diagnostic") == 0);
    free(line);
    line = NULL;

    rc = read_content_line_dynamic(f, &line);
    assert(rc == 1 && parse_prefixed_size_line(line,
                                               "EVOLUTION_STEPS ",
                                               &steps));
    free(line);
    line = NULL;

    rc = read_content_line_dynamic(f, &line);
    assert(rc == 1 && parse_prefixed_size_line(line, "ASSERTIONS ", &assertions));
    free(line);
    line = NULL;

    while ((rc = read_content_line_dynamic(f, &line)) == 1) {
        verify_algo_case(f, line, steps);
        seen++;
        free(line);
        line = NULL;
    }

    assert(rc == 0);
    assert(seen == assertions);
    fclose(f);

    printf("  %s: %zu Cook diagnostic case(s) PASS\n", path, seen);
}

static int run_algo_manifests(void) {
    size_t manifest_count =
        sizeof(ALGO_R110_MANIFESTS) / sizeof(ALGO_R110_MANIFESTS[0]);

    printf("== test_r110_round_trip --algo ==\n");
    for (size_t i = 0; i < manifest_count; i++) {
        verify_algo_manifest(ALGO_R110_MANIFESTS[i]);
    }
    printf("ALL algo r110 diagnostic tests passed\n");
    return 0;
}

int main(int argc, char **argv) {
    size_t manifest_count = sizeof(R110_MANIFESTS) / sizeof(R110_MANIFESTS[0]);

    if (argc == 2 && strcmp(argv[1], "--algo") == 0) {
        return run_algo_manifests();
    }
    assert(argc == 1);

    printf("== test_r110_round_trip ==\n");
    for (size_t i = 0; i < manifest_count; i++) {
        verify_manifest(R110_MANIFESTS[i]);
    }
    printf("ALL test_r110_round_trip tests passed\n");
    return 0;
}
