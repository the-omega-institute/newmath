#include "cook_decode.h"
#include "rule110.h"

#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/stat.h>
#include <unistd.h>

#define WORD_LEN 18u
#define EXPECTED_WORDS 21u
#define MAX_WORDS 4096u
#define MAX_PATH 256u
#define MAX_NAME 128u
#define DECODE_BUF 8192u

typedef struct {
    uint32_t key;
    char manifest[MAX_PATH];
    char case_name[MAX_NAME];
    size_t time;
    size_t start;
} WordHit;

typedef struct {
    WordHit hits[MAX_WORDS];
    size_t count;
    size_t replay_cases;
    size_t decoded_cases;
} Projection;

static const char *ALGO_MANIFESTS[] = {
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

static char *trim(char *s) {
    char *e;
    while (*s && isspace((unsigned char)*s)) s++;
    e = s + strlen(s);
    while (e > s && isspace((unsigned char)e[-1])) e--;
    *e = '\0';
    return s;
}

static int read_line(FILE *f, char **out) {
    size_t cap = 4096, len = 0;
    int ch;
    char *buf = (char *)malloc(cap);
    if (buf == NULL) return -1;
    while ((ch = fgetc(f)) != EOF) {
        if (len + 1 >= cap) {
            char *next = (char *)realloc(buf, cap * 2);
            if (next == NULL) {
                free(buf);
                return -1;
            }
            buf = next;
            cap *= 2;
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

static int read_content(FILE *f, char **out) {
    for (;;) {
        int rc = read_line(f, out);
        char *t;
        if (rc <= 0) return rc;
        t = trim(*out);
        if (t[0] == '\0' || t[0] == '#') {
            free(*out);
            continue;
        }
        if (t != *out) memmove(*out, t, strlen(t) + 1);
        return 1;
    }
}

static int parse_size(const char *s, size_t *out) {
    char *end = NULL;
    unsigned long v = strtoul(s, &end, 10);
    if (end == s) return 0;
    while (*end && isspace((unsigned char)*end)) end++;
    if (*end != '\0') return 0;
    *out = (size_t)v;
    return 1;
}

static int pref_size(const char *line, const char *prefix, size_t *out) {
    size_t n = strlen(prefix);
    return strncmp(line, prefix, n) == 0 && parse_size(line + n, out);
}

static int pref_text(const char *line, const char *prefix, char *out, size_t cap) {
    size_t n = strlen(prefix);
    size_t len;
    if (strncmp(line, prefix, n) != 0) return 0;
    len = strlen(line + n);
    if (len + 1 > cap) return 0;
    memcpy(out, line + n, len + 1);
    return 1;
}

static int bits_to_cells(const char *bits, size_t len, uint8_t **out) {
    uint8_t *cells;
    if (strlen(bits) != len) return 0;
    cells = (uint8_t *)malloc(len ? len : 1);
    if (cells == NULL) return 0;
    for (size_t i = 0; i < len; i++) {
        if (bits[i] != '0' && bits[i] != '1') {
            free(cells);
            return 0;
        }
        cells[i] = (uint8_t)(bits[i] == '1');
    }
    *out = cells;
    return 1;
}

static int read_cells(FILE *f, size_t len, uint8_t **out) {
    char *line = NULL;
    int rc = read_content(f, &line);
    int ok = rc == 1 && bits_to_cells(line, len, out);
    free(line);
    return ok;
}

static int same_cells(const uint8_t *a, const uint8_t *b, size_t len) {
    for (size_t i = 0; i < len; i++) {
        if ((a[i] ? 1u : 0u) != (b[i] ? 1u : 0u)) return 0;
    }
    return 1;
}

static int key_has_11(uint32_t key) {
    return (key & (key >> 1)) != 0u;
}

static void key_word(uint32_t key, char out[WORD_LEN + 1u]) {
    for (size_t i = 0; i < WORD_LEN; i++) {
        size_t shift = WORD_LEN - 1u - i;
        out[i] = ((key >> shift) & 1u) ? '1' : '0';
    }
    out[WORD_LEN] = '\0';
}

static int add_window(Projection *p,
                      uint32_t key,
                      const char *manifest,
                      const char *case_name,
                      size_t time,
                      size_t start) {
    if (key_has_11(key)) return 1;
    for (size_t i = 0; i < p->count; i++) {
        if (p->hits[i].key == key) return 1;
    }
    if (p->count >= MAX_WORDS) return 0;
    p->hits[p->count].key = key;
    p->hits[p->count].time = time;
    p->hits[p->count].start = start;
    if (strlen(manifest) >= sizeof(p->hits[p->count].manifest) ||
        strlen(case_name) >= sizeof(p->hits[p->count].case_name)) {
        return 0;
    }
    strcpy(p->hits[p->count].manifest, manifest);
    strcpy(p->hits[p->count].case_name, case_name);
    p->count++;
    return 1;
}

static int collect_decoded(Projection *p,
                           const char *manifest,
                           const char *case_name,
                           size_t time,
                           const char *decoded) {
    size_t len = strlen(decoded);
    if (len < WORD_LEN) return 1;
    for (size_t start = 0; start + WORD_LEN <= len; start++) {
        uint32_t key = 0;
        for (size_t i = 0; i < WORD_LEN; i++) {
            char ch = decoded[start + i];
            if (ch != 'N' && ch != 'Y') return 0;
            key = (key << 1) | (uint32_t)(ch == 'Y');
        }
        if (!add_window(p, key, manifest, case_name, time, start)) return 0;
    }
    return 1;
}

static int parse_case(FILE *f,
                      const char *manifest,
                      const char *case_line,
                      size_t steps,
                      Projection *p) {
    char case_name[MAX_NAME];
    char *line = NULL;
    uint8_t *initial = NULL, *expected = NULL, *cells = NULL, *ct = NULL;
    size_t initial_len = 0, expected_len = 0, ct_len = 0, ignored = 0;
    char decoded[DECODE_BUF];
    int rc, decode_rc, ok = 0;

    if (!pref_text(case_line, "case ", case_name, sizeof(case_name))) return 0;
    rc = read_content(f, &line);
    if (rc != 1 || strncmp(line, "INPUT ", 6) != 0) goto done;
    free(line); line = NULL;
    rc = read_content(f, &line);
    if (rc != 1 || !pref_size(line, "CT_STEPS ", &ignored)) goto done;
    free(line); line = NULL;
    rc = read_content(f, &line);
    if (rc != 1 || !pref_size(line, "CT_FINAL ", &ct_len)) goto done;
    free(line); line = NULL;
    if (!read_cells(f, ct_len, &ct)) goto done;
    rc = read_content(f, &line);
    if (rc != 1 || !pref_size(line, "RULE110_INITIAL ", &initial_len)) goto done;
    free(line); line = NULL;
    if (!read_cells(f, initial_len, &initial)) goto done;
    rc = read_content(f, &line);
    if (rc != 1 || !pref_size(line, "RULE110_FINAL ", &expected_len)) goto done;
    free(line); line = NULL;
    if (expected_len != initial_len || !read_cells(f, expected_len, &expected)) goto done;
    rc = read_content(f, &line);
    if (rc != 1 || strcmp(line, "ENDCASE") != 0) goto done;

    cells = (uint8_t *)malloc(initial_len ? initial_len : 1);
    if (cells == NULL) goto done;
    memcpy(cells, initial, initial_len);
    r110_run_n_steps(cells, initial_len, steps);
    if (!same_cells(cells, expected, initial_len)) goto done;
    p->replay_cases++;
    decode_rc = cook_decode_output(cells, initial_len, decoded, sizeof(decoded));
    if (decode_rc == COOK_DECODE_OK) {
        p->decoded_cases++;
        if (!collect_decoded(p, manifest, case_name, steps, decoded)) goto done;
    }
    ok = 1;

done:
    free(line);
    free(initial);
    free(expected);
    free(cells);
    free(ct);
    return ok;
}

static int collect_manifest(const char *path, Projection *p) {
    FILE *f = fopen(path, "r");
    char *line = NULL;
    char construction[64];
    size_t steps = 0, assertions = 0, seen = 0;
    int rc, diagnostic;
    if (f == NULL) return 0;
    rc = read_content(f, &line);
    if (rc != 1 || strcmp(line, "ALGO_R110_MANIFEST 1") != 0) goto fail;
    free(line); line = NULL;
    rc = read_content(f, &line);
    if (rc != 1 || strncmp(line, "SOURCE_CT ", 10) != 0) goto fail;
    free(line); line = NULL;
    rc = read_content(f, &line);
    if (rc != 1 || !pref_text(line, "CONSTRUCTION ", construction, sizeof(construction))) goto fail;
    diagnostic = strcmp(construction, "cook_phase_exact_packet_diagnostic") == 0;
    free(line); line = NULL;
    rc = read_content(f, &line);
    if (rc != 1 || !pref_size(line, "EVOLUTION_STEPS ", &steps)) goto fail;
    free(line); line = NULL;
    rc = read_content(f, &line);
    if (rc != 1 || !pref_size(line, "ASSERTIONS ", &assertions)) goto fail;
    free(line); line = NULL;
    if (!diagnostic) {
        fclose(f);
        return 1;
    }
    while ((rc = read_content(f, &line)) == 1) {
        if (strncmp(line, "case ", 5) != 0) goto fail;
        {
            char *case_line = line;
            line = NULL;
            if (!parse_case(f, path, case_line, steps, p)) {
                free(case_line);
                goto fail;
            }
            free(case_line);
        }
        seen++;
        free(line); line = NULL;
    }
    if (rc != 0 || seen != assertions) goto fail;
    fclose(f);
    return 1;
fail:
    free(line);
    fclose(f);
    return 0;
}

static int cmp_hit(const void *a, const void *b) {
    const WordHit *x = (const WordHit *)a;
    const WordHit *y = (const WordHit *)b;
    return x->key < y->key ? -1 : x->key > y->key ? 1 : 0;
}

static size_t fixed_row_baseline(void) {
    enum { TOTAL = 1u << WORD_LEN };
    unsigned char seen[TOTAL];
    memset(seen, 0, sizeof(seen));
    for (uint32_t x = 0; x < TOTAL; x++) {
        uint32_t y = 0;
        for (size_t i = 0; i < WORD_LEN; i++) {
            size_t shift = WORD_LEN - 1u - i;
            uint32_t left = i == 0 ? 0u : (x >> (shift + 1u)) & 1u;
            uint32_t self = (x >> shift) & 1u;
            uint32_t right = i + 1u == WORD_LEN ? 0u : (x >> (shift - 1u)) & 1u;
            uint32_t idx = (left << 2) | (self << 1) | right;
            uint32_t bit = ((0x6eu >> idx) & 1u);
            y = (y << 1) | bit;
        }
        if (!key_has_11(y)) seen[y] = 1;
    }
    size_t count = 0;
    for (size_t i = 0; i < TOTAL; i++) count += seen[i] ? 1u : 0u;
    return count;
}

static int write_tsv(const Projection *p, const char *path) {
    FILE *out;
    if (mkdir("experiments", 0777) != 0) {
        struct stat st;
        if (stat("experiments", &st) != 0 || !S_ISDIR(st.st_mode)) return 0;
    }
    if (mkdir("experiments/zeckendorf_projection", 0777) != 0) {
        struct stat st;
        if (stat("experiments/zeckendorf_projection", &st) != 0 ||
            !S_ISDIR(st.st_mode)) return 0;
    }
    out = fopen(path, "w");
    if (out == NULL) return 0;
    fprintf(out, "word\tlength\tsource_mode\tsource_manifest\tsource_case\tsource_time\tdecoded_window_start\tdecoded_window_end\tsymbol_map\tcontains_11\taccepted\n");
    for (size_t i = 0; i < p->count; i++) {
        char word[WORD_LEN + 1u];
        key_word(p->hits[i].key, word);
        fprintf(out, "%s\t%u\tcook_decoded_symbol_window\t%s\t%s\t%zu\t%zu\t%zu\tN0_Y1\tfalse\ttrue\n",
                word, WORD_LEN, p->hits[i].manifest, p->hits[i].case_name,
                p->hits[i].time, p->hits[i].start, p->hits[i].start + WORD_LEN);
    }
    fclose(out);
    return 1;
}

static int run_projection(void) {
    Projection p;
    const char *out = "experiments/zeckendorf_projection/words_18.tsv";
    size_t manifest_count = sizeof(ALGO_MANIFESTS) / sizeof(ALGO_MANIFESTS[0]);
    size_t baseline;
    memset(&p, 0, sizeof(p));
    for (size_t i = 0; i < manifest_count; i++) {
        if (!collect_manifest(ALGO_MANIFESTS[i], &p)) {
            fprintf(stderr, "reject: failed to parse %s\n", ALGO_MANIFESTS[i]);
            unlink(out);
            return 1;
        }
    }
    qsort(p.hits, p.count, sizeof(p.hits[0]), cmp_hit);
    baseline = fixed_row_baseline();
    printf("cook_decoded_unique=%zu replay_cases=%zu decoded_cases=%zu fixed_row_step1_unique=%zu\n",
           p.count, p.replay_cases, p.decoded_cases, baseline);
    if (baseline == EXPECTED_WORDS) {
        fprintf(stderr, "reject: fixed-row diagnostic collided with expected count\n");
        unlink(out);
        return 1;
    }
    if (p.count != EXPECTED_WORDS) {
        fprintf(stderr, "reject: Cook decoded unique count is %zu, expected %u\n",
                p.count, EXPECTED_WORDS);
        unlink(out);
        return 1;
    }
    if (!write_tsv(&p, out)) {
        fprintf(stderr, "reject: failed to emit words_18.tsv\n");
        unlink(out);
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc != 1) {
        fprintf(stderr, "usage: %s\n", argv[0]);
        return 2;
    }
    return run_projection();
}
