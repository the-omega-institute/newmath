#include "manifest_runner.h"
#include "cyclic_tag.h"
#include "rule110.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

/* Parse manifest file. Format (very simple line-based):
 *   # comment lines start with '#'
 *   PRODUCTIONS <N>
 *   <bit-string> for each production (N lines, blank line = empty production)
 *   ASSERTIONS <K>   (ignored at parse time; runner takes inputs directly)
 *
 * For Tasks 6-9, the runner is invoked by test_mark.c which already knows
 * the input bits and expected outputs (encoded in the test source as
 * assertions). The .ct manifest file contributes the PRODUCTIONS section
 * which defines the CT program. */

static char *bit_string_to_bytes(const char *s, size_t *out_len) {
    size_t n = strlen(s);
    char *b = (char *)malloc(n ? n : 1);
    size_t j = 0;
    for (size_t i = 0; i < n; i++) {
        if (s[i] == '0' || s[i] == '1') b[j++] = s[i] - '0';
    }
    *out_len = j;
    return b;
}

typedef struct {
    uint8_t **prods;
    size_t   *prod_lens;
    size_t    num_prods;
} ParsedManifest;

static int parse_manifest(const char *path, ParsedManifest *out) {
    FILE *f = fopen(path, "r");
    if (!f) return -1;
    char line[1024];
    out->num_prods = 0;
    out->prods = NULL;
    out->prod_lens = NULL;

    while (fgets(line, sizeof(line), f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        if (strncmp(line, "PRODUCTIONS", 11) == 0) {
            size_t n = (size_t)strtoul(line + 11, NULL, 10);
            out->num_prods = n;
            out->prods = (uint8_t **)calloc(n + 1, sizeof(uint8_t *));
            out->prod_lens = (size_t *)calloc(n + 1, sizeof(size_t));
            for (size_t i = 0; i < n; i++) {
                if (!fgets(line, sizeof(line), f)) { fclose(f); return -1; }
                /* trim newline */
                size_t L = strlen(line);
                if (L > 0 && line[L-1] == '\n') line[--L] = 0;
                size_t bl;
                char *bits = bit_string_to_bytes(line, &bl);
                out->prods[i] = (uint8_t *)bits;
                out->prod_lens[i] = bl;
            }
            break;
        }
    }
    fclose(f);
    /* Need at least one production for ct_run_until_halt to avoid divide-by-zero. */
    if (out->num_prods == 0) {
        /* Free the empty arrays allocated above when PRODUCTIONS was parsed as 0. */
        free(out->prods);
        free(out->prod_lens);
        out->num_prods = 1;
        out->prods = (uint8_t **)calloc(2, sizeof(uint8_t *));
        out->prod_lens = (size_t *)calloc(2, sizeof(size_t));
        out->prods[0] = (uint8_t *)malloc(1);
        out->prod_lens[0] = 0;
    }
    return 0;
}

static void free_manifest(ParsedManifest *m) {
    for (size_t i = 0; i < m->num_prods; i++) free(m->prods[i]);
    free(m->prods);
    free(m->prod_lens);
}

MrResult mr_run_ct_manifest(const char *manifest_path,
                            const char *input_bits,
                            const char *expected_final_tape,
                            size_t max_steps) {
    ParsedManifest m;
    if (parse_manifest(manifest_path, &m) != 0) {
        fprintf(stderr, "manifest load failed: %s\n", manifest_path);
        return MR_FAIL_LOAD;
    }
    size_t in_len;
    char *in_bytes = bit_string_to_bytes(input_bits, &in_len);

    CtState s;
    if (ct_init(&s, m.prods, m.prod_lens, m.num_prods,
                (uint8_t *)in_bytes, in_len, 8192) != 0) {
        free(in_bytes); free_manifest(&m); return MR_FAIL_LOAD;
    }
    CtHaltReason h = ct_run_until_halt(&s, max_steps);

    /* Compare final tape to expected. */
    size_t expected_len;
    char *expected_bytes = bit_string_to_bytes(expected_final_tape, &expected_len);

    MrResult result = MR_PASS;
    if (h != CT_HALT_EMPTY && h != CT_HALT_STEPLIMIT) {
        result = MR_FAIL_HALT_REASON;
    } else if (s.tape_len != expected_len ||
               memcmp(s.tape, expected_bytes, expected_len) != 0) {
        result = MR_FAIL_TAPE_MISMATCH;
        fprintf(stderr, "tape mismatch in %s: got len=%zu, expected len=%zu\n",
                manifest_path, s.tape_len, expected_len);
    }

    free(expected_bytes);
    free(in_bytes);
    ct_free(&s);
    free_manifest(&m);
    return result;
}

typedef struct {
    uint8_t *initial;
    size_t initial_len;
    size_t steps;
    uint8_t *expected;
    size_t expected_len;
} R110Manifest;

static void r110_manifest_init(R110Manifest *m) {
    m->initial = NULL;
    m->initial_len = 0;
    m->steps = 0;
    m->expected = NULL;
    m->expected_len = 0;
}

static void r110_manifest_free(R110Manifest *m) {
    free(m->initial);
    free(m->expected);
    r110_manifest_init(m);
}

static int read_manifest_line(FILE *f, char **out) {
    size_t cap = 128;
    size_t len = 0;
    int c;
    char *buf = (char *)malloc(cap);
    if (!buf) return -1;

    while ((c = fgetc(f)) != EOF) {
        if (len + 1 >= cap) {
            size_t next_cap = cap * 2;
            char *next = (char *)realloc(buf, next_cap);
            if (!next) {
                free(buf);
                return -1;
            }
            buf = next;
            cap = next_cap;
        }
        if (c == '\n') break;
        buf[len++] = (char)c;
    }

    if (c == EOF && len == 0) {
        free(buf);
        return 0;
    }

    if (len > 0 && buf[len - 1] == '\r') len--;
    buf[len] = '\0';
    *out = buf;
    return 1;
}

static char *trim_ascii(char *s) {
    char *end;

    while (*s && isspace((unsigned char)*s)) s++;
    end = s + strlen(s);
    while (end > s && isspace((unsigned char)end[-1])) end--;
    *end = '\0';
    return s;
}

static int parse_keyword_size_line(const char *line,
                                   const char *keyword,
                                   size_t *out) {
    size_t keyword_len = strlen(keyword);
    char *endptr;
    unsigned long value;

    if (strncmp(line, keyword, keyword_len) != 0) return 0;
    if (!isspace((unsigned char)line[keyword_len])) return 0;

    value = strtoul(line + keyword_len, &endptr, 10);
    if (endptr == line + keyword_len) return 0;
    while (*endptr && isspace((unsigned char)*endptr)) endptr++;
    if (*endptr != '\0') return 0;

    *out = (size_t)value;
    return 1;
}

static int parse_bit_line_exact(const char *line,
                                size_t expected_len,
                                uint8_t **out) {
    uint8_t *bits;
    size_t i;

    if (strlen(line) != expected_len) return 0;
    bits = (uint8_t *)malloc(expected_len ? expected_len : 1);
    if (!bits) return 0;

    for (i = 0; i < expected_len; i++) {
        if (line[i] != '0' && line[i] != '1') {
            free(bits);
            return 0;
        }
        bits[i] = (uint8_t)(line[i] == '1');
    }

    *out = bits;
    return 1;
}

static int next_r110_content_line(FILE *f, char **out) {
    for (;;) {
        int rc = read_manifest_line(f, out);
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

static int parse_r110_manifest(const char *path, R110Manifest *out) {
    FILE *f = fopen(path, "r");
    char *line = NULL;
    size_t declared_len = 0;
    int rc;

    if (!f) return -1;
    r110_manifest_init(out);

    rc = next_r110_content_line(f, &line);
    if (rc != 1 ||
        !parse_keyword_size_line(line, "INITIAL_PATTERN", &declared_len)) {
        free(line);
        fclose(f);
        return -1;
    }
    free(line);
    line = NULL;

    rc = next_r110_content_line(f, &line);
    if (rc != 1 ||
        !parse_bit_line_exact(line, declared_len, &out->initial)) {
        free(line);
        r110_manifest_free(out);
        fclose(f);
        return -1;
    }
    out->initial_len = declared_len;
    free(line);
    line = NULL;

    rc = next_r110_content_line(f, &line);
    if (rc != 1 ||
        !parse_keyword_size_line(line, "EVOLUTION_STEPS", &out->steps)) {
        free(line);
        r110_manifest_free(out);
        fclose(f);
        return -1;
    }
    free(line);
    line = NULL;

    rc = next_r110_content_line(f, &line);
    if (rc != 1 ||
        !parse_keyword_size_line(line, "EXPECTED_FINAL_PATTERN", &declared_len)) {
        free(line);
        r110_manifest_free(out);
        fclose(f);
        return -1;
    }
    free(line);
    line = NULL;

    rc = next_r110_content_line(f, &line);
    if (rc != 1 ||
        !parse_bit_line_exact(line, declared_len, &out->expected)) {
        free(line);
        r110_manifest_free(out);
        fclose(f);
        return -1;
    }
    out->expected_len = declared_len;
    free(line);
    fclose(f);

    if (out->initial_len != out->expected_len) {
        r110_manifest_free(out);
        return -1;
    }

    return 0;
}

static size_t count_cell_diffs(const uint8_t *a, const uint8_t *b, size_t len) {
    size_t diffs = 0;

    for (size_t i = 0; i < len; i++) {
        if (a[i] != b[i]) diffs++;
    }
    return diffs;
}

MrResult mr_run_r110_manifest(const char *manifest_path,
                              size_t max_diff_cells) {
    R110Manifest m;
    uint8_t *cells;
    size_t diff_cells;

    if (parse_r110_manifest(manifest_path, &m) != 0) {
        fprintf(stderr, "r110 manifest load failed: %s\n", manifest_path);
        return MR_FAIL_LOAD;
    }

    cells = (uint8_t *)malloc(m.initial_len ? m.initial_len : 1);
    if (!cells) {
        r110_manifest_free(&m);
        return MR_FAIL_LOAD;
    }
    memcpy(cells, m.initial, m.initial_len);

    r110_run_n_steps(cells, m.initial_len, m.steps);
    diff_cells = count_cell_diffs(cells, m.expected, m.expected_len);

    if (diff_cells > max_diff_cells) {
        fprintf(stderr,
                "r110 mismatch in %s: diff cells=%zu, tolerance=%zu, len=%zu, steps=%zu\n",
                manifest_path, diff_cells, max_diff_cells, m.expected_len, m.steps);
        free(cells);
        r110_manifest_free(&m);
        return MR_FAIL_TAPE_MISMATCH;
    }

    free(cells);
    r110_manifest_free(&m);
    return MR_PASS;
}
