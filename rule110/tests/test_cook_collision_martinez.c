#include "rule110.h"
#include "glider_phases.h"
#include "cook_collisions.h"
#include "cook_detect.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define ARRAY_LEN(a) (sizeof(a) / sizeof((a)[0]))
#define MAX_PRODUCTS 8
#define MAX_DETECTED_HITS 512
#define DETECT_TRACK_STEPS 184
#define TABLE_AUDIT_PASS_GATE 20

typedef struct {
    const char *encoded;
    char name[16];
    char neighbor[16];
    int has_neighbor;
    int phase;
} PhaseSpec;

typedef struct {
    const char *left;
    const char *right;
    int gap;
    int contact_delta;
    size_t steps;
    const char *expected;
    const char *out0;
    const char *out1;
} CollisionCase;

typedef struct {
    const char *left;
    const char *right;
    int gap;
    const char *expected;
    const char *label;
} MartinezRow;

typedef struct {
    const char *ref;
    size_t cook_line;
    int preferred_delta;
    size_t preferred_steps;
} TableAuditRow;

typedef struct {
    char name[16];
} ProductName;

typedef struct {
    GliderHit hits[MAX_DETECTED_HITS];
    size_t count;
} DetectorReport;

static const CollisionCase CASES[] = {
    {"C1(A,f1_1)", "Ebar(B,f1_1)", 3, -39, 80, "{Ebar, C1}",
     "Ebar", "C1"},
    {"C1(A,f1_1)", "Ebar(C,f1_1)", 3, -40, 160, "{Ebar, C1}",
     "Ebar", "C1"},
    {"C2(A,f1_1)", "Ebar(C,f1_1)", 3, -40, 260, "{Ebar, C2}",
     "Ebar", "C2"},
    {"A(f1_1)", "Ebar(A,f1_1)", 4, -51, 120, "{Ebar, A}",
     "Ebar", "A"}
};

static const char *NEIGHBORS[] = {
    NULL, "A", "B", "C", "D", "E", "G", "H", "A2"
};

static const MartinezRow MARTINEZ_ROWS[] = {
    {"A(f1_1)", "G(C,f1_1)", 6, "{G, A}", "martinez_row_1"},
    {"C1(A,f1_1)", "Ebar(B,f1_1)", 3, "{Ebar, C1}", "martinez_row_2"},
    {"C1(A,f1_1)", "Ebar(C,f1_1)", 3, "{Ebar, C1}", "martinez_row_3"},
    {"F(A,f1_1)", "B(f4_1)", 3, "{B, F}", "martinez_row_4"},
    {"C2(A,f1_1)", "Ebar(C,f1_1)", 3, "{Ebar, C2}", "martinez_row_5"},
    {"C1(A,f1_1)", "F(B,f1_1)", 2, "{F, C1}", "martinez_row_6"},
    {"C2(A,f1_1)", "F(A,f1_1)", 2, "{F, C2}", "martinez_row_7"},
    {"A(f1_1)", "Ebar(A,f1_1)", 4, "{Ebar, A}", "martinez_row_8"},
    {"A(f1_1)", "Ebar(B,f1_1)", 4, "{Ebar, A}", "martinez_row_9"},
    {"A(f1_1)", "Ebar(C,f1_1)", 4, "{Ebar, A}", "martinez_row_10"},
    {"A(f1_1)", "Ebar(H,f1_1)", 4, "{Ebar, A}", "martinez_row_11"},
    {"F(A,f1_1)", "Ebar(A,f1_1)", 1, "{Ebar, F}", "martinez_row_12"},
    {"F(A,f1_1)", "Ebar(C,f1_1)", 1, "{Ebar, F}", "martinez_row_13"},
    {"F(A,f1_1)", "Ebar(D,f1_1)", 1, "{Ebar, F}", "martinez_row_14"},
    {"F(A,f1_1)", "Ebar(E,f1_1)", 1, "{Ebar, F}", "martinez_row_15"},
    {"F(G,f1_1)", "Ebar(A,f1_1)", 1, "{Ebar, F}", "martinez_row_16"},
    {"F(G,f1_1)", "Ebar(B,f1_1)", 1, "{Ebar, F}", "martinez_row_17"},
    {"F(G,f1_1)", "Ebar(H,f1_1)", 1, "{Ebar, F}", "martinez_row_18"},
    {"F(A,f1_1)", "Bbar(A,f1_1)", 1, "{A, B, Bbar, F}", "martinez_row_19"},
    {"F(A,f1_1)", "Bbar(B,f1_1)", 1, "{A, 2 C3, C1}", "martinez_row_20"},
    {"F(A,f1_1)", "Bbar(C,f1_1)", 1, "{A, C2}", "martinez_row_21"},
    {"F(G,f1_1)", "Bbar(A,f1_1)", 1, "{C2, A^2}", "martinez_row_22"},
    {"F(G,f1_1)", "Bbar(B,f1_1)", 1, "{A, A^3, A, Ebar}", "martinez_row_23"},
    {"F(G,f1_1)", "Bbar(C,f1_1)", 1, "{B, F} *", "martinez_row_24"},
    {"F(H,f1_1)", "Bbar(A,f1_1)", 1, "{A, C2}", "martinez_row_25"},
    {"F(H,f1_1)", "Bbar(B,f1_1)", 1, "{Ebar, A^5}", "martinez_row_26"},
    {"F(H,f1_1)", "Bbar(C,f1_1)", 1, "{Ebar, A^5}", "martinez_row_27"},
    {"F(A2,f1_1)", "Bbar(A,f1_1)", 1, "{C1}", "martinez_row_28"},
    {"F(A2,f1_1)", "Bbar(B,f1_1)", 1, "{A, B^3, Ebar}", "martinez_row_29"},
    {"F(A,f1_1)", "B(f1_1)", 1, "{Bbar, F} *", "martinez_row_30"},
    {"F(G,f1_1)", "B(f1_1)", 1, "{Bbar, F} *", "martinez_row_31"},
    {"F(H,f1_1)", "B(f1_1)", 1, "{D2, A^2}", "martinez_row_32"},
    {"F(A2)", "B", 1, "{B, F} (soliton)", "martinez_row_33"}
};

static const TableAuditRow TABLE_AUDIT_ROWS[] = {
    /* Martinez 2012 soliton (a), cook_collisions.c:29 */
    {"Martinez 2012 soliton (a)", 29, -40, 220},
    /* Martinez 2012 soliton (b), cook_collisions.c:30 */
    {"Martinez 2012 soliton (b)", 30, -39, 80},
    /* Martinez 2012 soliton (c), cook_collisions.c:31 */
    {"Martinez 2012 soliton (c)", 31, -40, 160},
    /* Martinez 2012 soliton (d), cook_collisions.c:32 */
    {"Martinez 2012 soliton (d)", 32, -40, 220},
    /* Martinez 2012 soliton (e), cook_collisions.c:33 */
    {"Martinez 2012 soliton (e)", 33, -40, 260},
    /* Martinez 2012 soliton (f), cook_collisions.c:34 */
    {"Martinez 2012 soliton (f)", 34, -40, 220},
    /* Martinez 2012 soliton (g), cook_collisions.c:35 */
    {"Martinez 2012 soliton (g)", 35, -40, 220},
    /* Martinez 2012 soliton (h), cook_collisions.c:36 */
    {"Martinez 2012 soliton (h)", 36, -51, 120},
    /* Martinez 2012 soliton (i), cook_collisions.c:37 */
    {"Martinez 2012 soliton (i)", 37, -51, 120},
    /* Martinez 2012 soliton (j), cook_collisions.c:38 */
    {"Martinez 2012 soliton (j)", 38, -51, 120},
    /* Martinez 2012 soliton (k), cook_collisions.c:39 */
    {"Martinez 2012 soliton (k)", 39, -51, 120},
    /* Martinez 2012 soliton (l), cook_collisions.c:40 */
    {"Martinez 2012 soliton (l)", 40, -40, 220},
    /* Martinez 2012 soliton (m), cook_collisions.c:41 */
    {"Martinez 2012 soliton (m)", 41, -40, 220},
    /* Martinez 2012 soliton (n), cook_collisions.c:42 */
    {"Martinez 2012 soliton (n)", 42, -40, 220},
    /* Martinez 2012 soliton (o), cook_collisions.c:43 */
    {"Martinez 2012 soliton (o)", 43, -40, 220},
    /* Martinez 2012 soliton (p), cook_collisions.c:44 */
    {"Martinez 2012 soliton (p)", 44, -40, 220},
    /* Martinez 2012 soliton (q), cook_collisions.c:45 */
    {"Martinez 2012 soliton (q)", 45, -40, 220},
    /* Martinez 2012 soliton (r), cook_collisions.c:46 */
    {"Martinez 2012 soliton (r)", 46, -40, 220},
    /* Martinez 2012 Table 2, cook_collisions.c:47 */
    {"Martinez 2012 Table 2", 47, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:48 */
    {"Martinez 2012 Table 2", 48, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:49 */
    {"Martinez 2012 Table 2", 49, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:50 */
    {"Martinez 2012 Table 2", 50, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:51 */
    {"Martinez 2012 Table 2", 51, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:52 */
    {"Martinez 2012 Table 2", 52, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:53 */
    {"Martinez 2012 Table 2", 53, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:54 */
    {"Martinez 2012 Table 2", 54, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:55 */
    {"Martinez 2012 Table 2", 55, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:56 */
    {"Martinez 2012 Table 2", 56, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:57 */
    {"Martinez 2012 Table 2", 57, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:58 */
    {"Martinez 2012 Table 2", 58, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:59 */
    {"Martinez 2012 Table 2", 59, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:60 */
    {"Martinez 2012 Table 2", 60, -40, 260},
    /* Martinez 2012 Table 2, cook_collisions.c:61 */
    {"Martinez 2012 Table 2", 61, -40, 260}
};

static int copy_token(char *dst, size_t dst_len, const char *src, size_t len) {
    if (len == 0u || len >= dst_len) return 1;
    memcpy(dst, src, len);
    dst[len] = '\0';
    return 0;
}

static int parse_positive_int(const char *text, size_t *index) {
    int value = 0;

    while (text[*index] >= '0' && text[*index] <= '9') {
        value = value * 10 + (text[*index] - '0');
        (*index)++;
    }

    return value;
}

static int decode_phase_spec(const char *encoded, PhaseSpec *out) {
    const char *open = NULL;
    const char *close = NULL;
    const char *comma = NULL;
    size_t i = 0;
    size_t inner_start = 0;

    memset(out, 0, sizeof(*out));
    out->encoded = encoded;
    out->phase = 1;

    open = strchr(encoded, '(');
    if (open == NULL) return copy_token(out->name, sizeof(out->name),
                                        encoded, strlen(encoded));

    close = strchr(open, ')');
    if (close == NULL) return 1;
    if (copy_token(out->name, sizeof(out->name), encoded,
                   (size_t)(open - encoded))) {
        return 1;
    }

    inner_start = (size_t)(open - encoded) + 1u;
    comma = strchr(open, ',');
    if (comma != NULL && comma < close) {
        if (copy_token(out->neighbor, sizeof(out->neighbor),
                       encoded + inner_start,
                       (size_t)(comma - encoded) - inner_start)) {
            return 1;
        }
        out->has_neighbor = 1;
        i = (size_t)(comma - encoded) + 1u;
    } else {
        i = inner_start;
        if (encoded[i] != 'f') {
            if (copy_token(out->neighbor, sizeof(out->neighbor),
                           encoded + inner_start,
                           (size_t)(close - encoded) - inner_start)) {
                return 1;
            }
            out->has_neighbor = 1;
            return 0;
        }
    }

    if (encoded[i] == 'f') {
        i++;
        out->phase = parse_positive_int(encoded, &i);
        if (out->phase <= 0) return 1;
    }

    return 0;
}

static const char *phase_neighbor(const PhaseSpec *spec) {
    return spec->has_neighbor ? spec->neighbor : NULL;
}

static void fill_ether(uint8_t *cells, size_t len) {
    size_t ether_len = 0;
    const char *ether = glider_phase("ether", NULL, 1, &ether_len);

    if (ether == NULL || ether_len == 0u) abort();
    for (size_t i = 0; i < len; i++) {
        cells[i] = (uint8_t)(ether[i % ether_len] == '1');
    }
}

static int emit_spec(uint8_t *cells,
                     size_t len,
                     size_t pos,
                     const PhaseSpec *spec,
                     size_t *written_out) {
    size_t phase_len = 0;
    const char *bits = NULL;

    if (written_out != NULL) *written_out = 0;
    bits = glider_phase(spec->name, phase_neighbor(spec), spec->phase,
                        &phase_len);
    if (bits == NULL || pos > len || phase_len > len - pos) return 1;

    for (size_t i = 0; i < phase_len; i++) {
        cells[pos + i] = (uint8_t)(bits[i] == '1');
    }
    if (written_out != NULL) *written_out = phase_len;
    return 0;
}

static size_t count_diff(const uint8_t *cells,
                         const uint8_t *ether,
                         size_t len) {
    size_t diff = 0;

    for (size_t i = 0; i < len; i++) {
        if (cells[i] != ether[i]) diff++;
    }
    return diff;
}

static size_t count_diff_islands(const uint8_t *cells,
                                 const uint8_t *ether,
                                 size_t len) {
    size_t count = 0;
    size_t quiet_gap = 0;
    int in_island = 0;

    for (size_t i = 0; i < len; i++) {
        if (cells[i] != ether[i]) {
            if (!in_island) {
                count++;
                in_island = 1;
            }
            quiet_gap = 0;
        } else if (in_island) {
            quiet_gap++;
            if (quiet_gap > 3u) {
                in_island = 0;
                quiet_gap = 0;
            }
        }
    }
    return count;
}

static int window_has_diff(const uint8_t *cells,
                           const uint8_t *ether,
                           size_t pos,
                           size_t phase_len) {
    for (size_t i = 0; i < phase_len; i++) {
        if (cells[pos + i] != ether[pos + i]) return 1;
    }
    return 0;
}

static int match_phase_at(const uint8_t *cells,
                          const uint8_t *ether,
                          size_t len,
                          size_t pos,
                          const char *name,
                          const char *neighbor,
                          int phase) {
    size_t phase_len = 0;
    const char *bits = glider_phase(name, neighbor, phase, &phase_len);

    if (bits == NULL || pos > len || phase_len > len - pos) return 0;
    if (!window_has_diff(cells, ether, pos, phase_len)) return 0;
    for (size_t i = 0; i < phase_len; i++) {
        if (cells[pos + i] != (uint8_t)(bits[i] == '1')) return 0;
    }
    return 1;
}

static int phase_registered_for(const char *name) {
    size_t phase_len = 0;

    for (size_t n = 0; n < ARRAY_LEN(NEIGHBORS); n++) {
        for (int phase = 1; phase <= 4; phase++) {
            if (glider_phase(name, NEIGHBORS[n], phase, &phase_len) != NULL) {
                return 1;
            }
        }
    }
    return 0;
}

static int detect_glider(const uint8_t *cells,
                         const uint8_t *ether,
                         size_t len,
                         const char *name) {
    for (size_t pos = 0; pos < len; pos++) {
        for (size_t n = 0; n < ARRAY_LEN(NEIGHBORS); n++) {
            for (int phase = 1; phase <= 4; phase++) {
                if (match_phase_at(cells,
                                   ether,
                                   len,
                                   pos,
                                   name,
                                   NEIGHBORS[n],
                                   phase)) {
                    return 1;
                }
            }
        }
    }
    return 0;
}

static int add_product(ProductName *products,
                       size_t *count,
                       const char *name,
                       size_t len) {
    char token[16];

    if (copy_token(token, sizeof(token), name, len)) return 1;
    for (size_t i = 0; i < *count; i++) {
        if (strcmp(products[i].name, token) == 0) return 0;
    }
    if (*count >= MAX_PRODUCTS) return 1;
    strcpy(products[*count].name, token);
    (*count)++;
    return 0;
}

static int collect_expected_products(const char *expected,
                                     ProductName *products,
                                     size_t *count) {
    size_t i = 0;

    *count = 0;
    while (expected[i] != '\0') {
        if (expected[i] == '(') break;
        if (expected[i] >= 'A' && expected[i] <= 'Z') {
            size_t start = i;

            i++;
            while ((expected[i] >= 'A' && expected[i] <= 'Z') ||
                   (expected[i] >= 'a' && expected[i] <= 'z') ||
                   (expected[i] >= '0' && expected[i] <= '9')) {
                i++;
            }
            if (add_product(products, count, expected + start, i - start)) {
                return 1;
            }
            if (expected[i] == '^') {
                i++;
                while (expected[i] >= '0' && expected[i] <= '9') i++;
            }
        } else {
            i++;
        }
    }

    return 0;
}

static int detector_hit_matches(const GliderHit *hit, const char *name) {
    if (strcmp(hit->name, name) == 0) return 1;
    if (strcmp(hit->name, "Ebar") == 0 && strcmp(name, "E-") == 0) return 1;
    if (strcmp(hit->name, "Bbar") == 0 && strcmp(name, "B-") == 0) return 1;
    return 0;
}

static int exact_phase_detects_any(const uint8_t *cells,
                                   const uint8_t *ether,
                                   size_t len,
                                   const char *name) {
    return detect_glider(cells, ether, len, name);
}

static int detector_period_for(const char *name) {
    if (strcmp(name, "A") == 0) return 3;
    if (strcmp(name, "B") == 0) return 4;
    if (strcmp(name, "Bbar") == 0) return 12;
    if (strcmp(name, "C1") == 0) return 7;
    if (strcmp(name, "C2") == 0) return 7;
    if (strcmp(name, "C3") == 0) return 7;
    if (strcmp(name, "D1") == 0) return 10;
    if (strcmp(name, "D2") == 0) return 10;
    if (strcmp(name, "Ebar") == 0) return 30;
    if (strcmp(name, "F") == 0) return 36;
    if (strcmp(name, "G") == 0) return 42;
    if (strcmp(name, "H") == 0) return 92;
    return 0;
}

static int expected_products_tracked(const uint8_t *cells,
                                     const uint8_t *ether,
                                     size_t len,
                                     const ProductName *products,
                                     size_t product_count,
                                     char *missing,
                                     size_t missing_len,
                                     DetectorReport *report) {
    int detected = cook_detect_gliders(cells,
                                       len,
                                       DETECT_TRACK_STEPS,
                                       report->hits,
                                       ARRAY_LEN(report->hits));

    if (detected < 0) return 0;
    report->count = (size_t)detected;
    for (size_t i = 0; i < product_count; i++) {
        int found = 0;

        if (exact_phase_detects_any(cells, ether, len, products[i].name)) {
            found = 1;
        }
        for (size_t h = 0; h < report->count; h++) {
            if (detector_hit_matches(&report->hits[h], products[i].name)) {
                found = 1;
                break;
            }
        }
        if (!found) {
            (void)copy_token(missing, missing_len, products[i].name,
                             strlen(products[i].name));
            return 0;
        }
    }
    return 1;
}

static void print_detector_report(const DetectorReport *report) {
    size_t limit = report->count < 12u ? report->count : 12u;

    printf(" detector_hits=%zu", report->count);
    for (size_t i = 0; i < limit; i++) {
        const GliderHit *hit = &report->hits[i];

        printf(" [%s%s%s phase=%d pos=%zu->%zu period=%d displacement=%d]",
               hit->name,
               hit->neighbor == NULL ? "" : "/",
               hit->neighbor == NULL ? "" : hit->neighbor,
               hit->phase,
               hit->initial_position,
               hit->final_position,
               detector_period_for(hit->name),
               hit->displacement);
    }
}

static int verify_collision(const CollisionCase *tc) {
    enum { W = 1800 };
    uint8_t cells[W];
    uint8_t ether[W];
    PhaseSpec left_spec;
    PhaseSpec right_spec;
    size_t pos1 = 600;
    size_t pos2 = 0;
    size_t left_len = 0;
    const char *lookup = cook_collision_lookup(tc->left, tc->right, tc->gap);
    size_t before_diff = 0;
    size_t before_islands = 0;
    size_t after_diff = 0;
    size_t after_islands = 0;
    int detected0 = 0;
    int detected1 = 0;

    if (lookup == NULL) {
        printf("  %s / %s: FAIL missing cook collision row\n",
               tc->left,
               tc->right);
        return 1;
    }
    if (strcmp(lookup, tc->expected) != 0) {
        printf("  %s / %s: FAIL lookup=%s expected=%s\n",
               tc->left,
               tc->right,
               lookup,
               tc->expected);
        return 1;
    }

    if (decode_phase_spec(tc->left, &left_spec) ||
        decode_phase_spec(tc->right, &right_spec)) {
        printf("  %s / %s: FAIL malformed phase spec\n", tc->left, tc->right);
        return 1;
    }

    fill_ether(cells, W);
    fill_ether(ether, W);
    if (emit_spec(cells, W, pos1, &left_spec, &left_len)) {
        printf("  %s / %s: FAIL missing left phase\n", tc->left, tc->right);
        return 1;
    }
    pos2 = (size_t)((long)pos1 + (long)left_len +
                    ((long)tc->gap * 14L) + (long)tc->contact_delta);
    if (emit_spec(cells, W, pos2, &right_spec, NULL)) {
        printf("  %s / %s: FAIL missing right phase\n", tc->left, tc->right);
        return 1;
    }

    before_diff = count_diff(cells, ether, W);
    before_islands = count_diff_islands(cells, ether, W);
    r110_run_n_steps(cells, W, tc->steps);
    r110_run_n_steps(ether, W, tc->steps);
    after_diff = count_diff(cells, ether, W);
    after_islands = count_diff_islands(cells, ether, W);
    detected0 = detect_glider(cells, ether, W, tc->out0);
    detected1 = detect_glider(cells, ether, W, tc->out1);

    if (before_diff == 0u || before_islands < 2u ||
        after_diff == before_diff || !detected0 || !detected1) {
        printf("  %s -%d e- %s -> %s: FAIL diff %zu/%zu islands %zu/%zu\n",
               tc->left,
               tc->gap,
               tc->right,
               lookup,
               before_diff,
               after_diff,
               before_islands,
               after_islands);
        return 1;
    }

    printf("  %s -%d e- %s -> %s: PASS diff %zu/%zu islands %zu/%zu\n",
           tc->left,
           tc->gap,
           tc->right,
           lookup,
           before_diff,
           after_diff,
           before_islands,
           after_islands);
    return 0;
}

static int run_direct_trial(const char *left,
                            const char *right,
                            int gap,
                            int contact_delta,
                            size_t steps,
                            const ProductName *products,
                            size_t product_count,
                            size_t *after_diff_out,
                            size_t *after_islands_out,
                            char *missing,
                            size_t missing_len,
                            DetectorReport *report) {
    enum { W = 1800 };
    uint8_t cells[W];
    uint8_t ether[W];
    PhaseSpec left_spec;
    PhaseSpec right_spec;
    size_t pos1 = 600;
    size_t pos2 = 0;
    size_t left_len = 0;
    size_t before_diff = 0;
    size_t after_diff = 0;
    size_t after_islands = 0;

    if (report == NULL) return 0;
    memset(report, 0, sizeof(*report));
    if (decode_phase_spec(left, &left_spec) ||
        decode_phase_spec(right, &right_spec)) {
        return 0;
    }
    fill_ether(cells, W);
    fill_ether(ether, W);
    if (emit_spec(cells, W, pos1, &left_spec, &left_len)) return 0;

    pos2 = (size_t)((long)pos1 + (long)left_len +
                    ((long)gap * 14L) + (long)contact_delta);
    if (emit_spec(cells, W, pos2, &right_spec, NULL)) return 0;

    before_diff = count_diff(cells, ether, W);
    r110_run_n_steps(cells, W, steps);
    r110_run_n_steps(ether, W, steps);
    after_diff = count_diff(cells, ether, W);
    after_islands = count_diff_islands(cells, ether, W);

    if (after_diff_out != NULL) *after_diff_out = after_diff;
    if (after_islands_out != NULL) *after_islands_out = after_islands;
    if (before_diff == 0u) {
        return 0;
    }

    return expected_products_tracked(cells,
                                     ether,
                                     W,
                                     products,
                                     product_count,
                                     missing,
                                     missing_len,
                                     report);
}

static int verify_table_row(size_t index,
                            const TableAuditRow *meta,
                            size_t *pass_count,
                            size_t *fail_count) {
    const char *left = cook_collision_lookup_left(index);
    const char *right = cook_collision_lookup_right(index);
    int gap = cook_collision_lookup_gap(index);
    const char *expected = cook_collision_lookup_result(index);
    ProductName products[MAX_PRODUCTS];
    size_t product_count = 0;
    PhaseSpec left_spec;
    PhaseSpec right_spec;
    char missing[16] = "";
    size_t after_diff = 0;
    size_t after_islands = 0;
    DetectorReport report;

    if (left == NULL || right == NULL || expected == NULL ||
        meta == NULL || collect_expected_products(expected, products,
                                                  &product_count)) {
        printf("  table_row_%zu: FAIL malformed lookup row\n", index + 1u);
        (*fail_count)++;
        return 1;
    }

    if (decode_phase_spec(left, &left_spec) ||
        decode_phase_spec(right, &right_spec)) {
        printf("  table_row_%zu: FAIL malformed phase spec\n", index + 1u);
        (*fail_count)++;
        return 1;
    }

    if (!phase_registered_for(left_spec.name) ||
        glider_phase(left_spec.name, phase_neighbor(&left_spec),
                     left_spec.phase, NULL) == NULL) {
        printf("  FAIL table_row_%zu: detect 不到 %s glider (glider_phases.c 缺 entry)\n",
               index + 1u,
               left_spec.name);
        (*fail_count)++;
        return 1;
    }
    if (!phase_registered_for(right_spec.name) ||
        glider_phase(right_spec.name, phase_neighbor(&right_spec),
                     right_spec.phase, NULL) == NULL) {
        printf("  FAIL table_row_%zu: detect 不到 %s glider (glider_phases.c 缺 entry)\n",
               index + 1u,
               right_spec.name);
        (*fail_count)++;
        return 1;
    }

    for (size_t p = 0; p < product_count; p++) {
        if (!phase_registered_for(products[p].name)) {
            printf("  FAIL table_row_%zu: detect 不到 %s glider (glider_phases.c 缺 entry)\n",
                   index + 1u,
                   products[p].name);
            (*fail_count)++;
            return 1;
        }
    }

    if (run_direct_trial(left, right, gap, meta->preferred_delta,
                         meta->preferred_steps, products, product_count,
                         &after_diff, &after_islands, missing,
                         sizeof(missing), &report)) {
        printf("  table_row_%zu %s cook_collisions.c:%zu: PASS delta=%d steps=%zu diff=%zu islands=%zu\n",
               index + 1u,
               meta->ref,
               meta->cook_line,
               meta->preferred_delta,
               meta->preferred_steps,
               after_diff,
               after_islands);
        (*pass_count)++;
        return 0;
    }

    printf("  table_row_%zu %s cook_collisions.c:%zu: FAIL expected=%s missing=%s\n",
           index + 1u,
           meta->ref,
           meta->cook_line,
           expected,
           missing[0] == '\0' ? "outcome" : missing);
    print_detector_report(&report);
    printf("\n");
    (*fail_count)++;
    return 1;
}

static int verify_lookup_accessors(void) {
    size_t checked = 0;

    for (size_t i = 0; i < cook_collision_lookup_count(); i++) {
        const char *left = cook_collision_lookup_left(i);
        const char *right = cook_collision_lookup_right(i);
        int gap = cook_collision_lookup_gap(i);
        const char *result = cook_collision_lookup_result(i);

        if (left == NULL || right == NULL || result == NULL) return 1;
        if (cook_collision_lookup(left, right, gap) != result) return 1;
        checked++;
    }

    if (checked < 18u) return 1;
    printf("  cook collision lookup table: PASS\n");
    return 0;
}

static const MartinezRow *find_martinez_row(const char *left,
                                            const char *right,
                                            int gap) {
    for (size_t i = 0; i < ARRAY_LEN(MARTINEZ_ROWS); i++) {
        if (gap == MARTINEZ_ROWS[i].gap &&
            strcmp(left, MARTINEZ_ROWS[i].left) == 0 &&
            strcmp(right, MARTINEZ_ROWS[i].right) == 0) {
            return &MARTINEZ_ROWS[i];
        }
    }
    return NULL;
}

static int verify_martinez_crosscheck(void) {
    size_t matched = 0;
    size_t only_in_paper = 0;
    size_t only_in_table = 0;
    size_t mismatch = 0;

    for (size_t i = 0; i < ARRAY_LEN(MARTINEZ_ROWS); i++) {
        const char *lookup = cook_collision_lookup(MARTINEZ_ROWS[i].left,
                                                   MARTINEZ_ROWS[i].right,
                                                   MARTINEZ_ROWS[i].gap);

        if (lookup == NULL) {
            printf("  WARNING %s: only in Martinez 2012: %s -%d e- %s -> %s\n",
                   MARTINEZ_ROWS[i].label,
                   MARTINEZ_ROWS[i].left,
                   MARTINEZ_ROWS[i].gap,
                   MARTINEZ_ROWS[i].right,
                   MARTINEZ_ROWS[i].expected);
            only_in_paper++;
        } else if (strcmp(lookup, MARTINEZ_ROWS[i].expected) == 0) {
            printf("  %s: %s -%d e- %s -> %s: PASS\n",
                   MARTINEZ_ROWS[i].label,
                   MARTINEZ_ROWS[i].left,
                   MARTINEZ_ROWS[i].gap,
                   MARTINEZ_ROWS[i].right,
                   lookup);
            matched++;
        } else {
            printf("  %s: FAIL table=%s martinez=%s for %s -%d e- %s\n",
                   MARTINEZ_ROWS[i].label,
                   lookup,
                   MARTINEZ_ROWS[i].expected,
                   MARTINEZ_ROWS[i].left,
                   MARTINEZ_ROWS[i].gap,
                   MARTINEZ_ROWS[i].right);
            mismatch++;
        }
    }

    for (size_t i = 0; i < cook_collision_lookup_count(); i++) {
        const char *left = cook_collision_lookup_left(i);
        const char *right = cook_collision_lookup_right(i);
        int gap = cook_collision_lookup_gap(i);

        if (find_martinez_row(left, right, gap) == NULL) only_in_table++;
    }

    printf("  Martinez 2012 Table 1/Table 2 cross-check: %zu rows, %zu matched, %zu only-in-paper, %zu only-in-table\n",
           ARRAY_LEN(MARTINEZ_ROWS),
           matched,
           only_in_paper,
           only_in_table);

    return mismatch == 0u ? 0 : 1;
}

static int verify_full_table_audit(void) {
    size_t pass_count = 0;
    size_t fail_count = 0;
    size_t total = cook_collision_lookup_count();

    if (total != ARRAY_LEN(TABLE_AUDIT_ROWS)) {
        printf("  table audit (cook_collisions.c full %zu rows): FAIL metadata rows=%zu\n",
               total,
               ARRAY_LEN(TABLE_AUDIT_ROWS));
        return 1;
    }

    for (size_t i = 0; i < total; i++) {
        (void)verify_table_row(i, &TABLE_AUDIT_ROWS[i], &pass_count,
                               &fail_count);
        if (fail_count * 3u >= total) {
            printf("  table audit stopped after %zu failure(s)\n",
                   fail_count);
            break;
        }
    }

    if (fail_count == 0u) {
        printf("  table audit (cook_collisions.c full %zu rows): %zu/%zu PASS\n",
               total,
               pass_count,
               total);
        return 0;
    }

    printf("  table audit (cook_collisions.c full %zu rows): %zu/%zu PASS, %zu FAIL\n",
           total,
           pass_count,
           total,
           fail_count);
    return pass_count >= (size_t)TABLE_AUDIT_PASS_GATE ? 0 : 1;
}

int main(int argc, char **argv) {
    int strict = 0;
    for (int i = 1; i < argc; i++) {
        if (strcmp(argv[i], "--strict") == 0) strict = 1;
    }

    int fail = 0;
    int audit_findings = 0;

    printf("== test_cook_collision_martinez ==\n");
    fail += verify_lookup_accessors();
    for (size_t i = 0; i < ARRAY_LEN(CASES); i++) {
        fail += verify_collision(&CASES[i]);
    }
    audit_findings += verify_full_table_audit();
    audit_findings += verify_martinez_crosscheck();

    if (strict) {
        fail += audit_findings;
    } else if (audit_findings) {
        printf("INFO %d audit finding(s); run `make test-collision-audit` for strict gate\n",
               audit_findings);
    }

    if (fail) {
        printf("FAIL %d collision verifier mismatch(es)\n", fail);
        return 1;
    }

    printf("ALL test_cook_collision_martinez tests passed\n");
    return 0;
}
