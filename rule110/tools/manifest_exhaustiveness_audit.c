#include "groundcompiler_encoding.h"

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_ITEMS 4096
#define MAX_STR 256
#define MAX_LINE 2048
#define MAX_GAPS_PRINTED 24

typedef struct {
    char text[MAX_STR];
} Item;

typedef struct {
    Item items[MAX_ITEMS];
    size_t count;
} ItemSet;

typedef struct {
    const char *type_name;
    const char *theorem_name;
    const char *manifest_path;
    int closure_depth;
    const char *depth_note;
    int (*enumerate)(int depth, ItemSet *out);
} AuditTarget;

static void itemset_init(ItemSet *set) {
    set->count = 0;
}

static int itemset_contains(const ItemSet *set, const char *text) {
    size_t i;

    for (i = 0; i < set->count; i++) {
        if (strcmp(set->items[i].text, text) == 0) return 1;
    }
    return 0;
}

static int itemset_add(ItemSet *set, const char *text) {
    if (strlen(text) >= MAX_STR) return 0;
    if (itemset_contains(set, text)) return 1;
    if (set->count >= MAX_ITEMS) return 0;
    strcpy(set->items[set->count].text, text);
    set->count++;
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

static int parse_manifest_inputs(const char *path, ItemSet *unique_inputs, size_t *raw_count) {
    FILE *f;
    char line[MAX_LINE];

    itemset_init(unique_inputs);
    *raw_count = 0;

    f = fopen(path, "r");
    if (!f) return 0;

    while (fgets(line, sizeof(line), f)) {
        char *trimmed = trim_ascii(line);
        char *start;
        char *end;
        char saved;
        char value[MAX_STR];

        if (strncmp(trimmed, "case ", 5) != 0) continue;
        start = strstr(trimmed, "input=");
        if (start != NULL) {
            start += 6;
        } else {
            start = strstr(trimmed, "display=");
            if (start == NULL) {
                fclose(f);
                return 0;
            }
            start += 8;
        }

        while (*start && isspace((unsigned char)*start)) start++;
        end = start;
        while (*end && !isspace((unsigned char)*end) && *end != ';') end++;
        saved = *end;
        *end = '\0';

        if (strcmp(start, "<empty>") == 0) {
            value[0] = '\0';
        } else {
            if (strlen(start) >= sizeof(value)) {
                fclose(f);
                return 0;
            }
            strcpy(value, start);
        }

        *end = saved;
        if (!itemset_add(unique_inputs, value)) {
            fclose(f);
            return 0;
        }
        (*raw_count)++;
    }

    fclose(f);
    return 1;
}

static int append_text(char *out, size_t cap, size_t *off, const char *src) {
    size_t len = strlen(src);

    if (*off + len >= cap) return 0;
    memcpy(out + *off, src, len);
    *off += len;
    out[*off] = '\0';
    return 1;
}

static int event_bits_from_payload(const uint8_t *payload,
                                   size_t payload_len,
                                   char *out,
                                   size_t cap) {
    uint8_t bits[MAX_STR];
    size_t n;
    size_t i;

    n = gc_event_encode(payload, payload_len, bits, sizeof(bits));
    if (n == 0 && payload_len != 0) return 0;
    if (n >= cap) return 0;
    for (i = 0; i < n; i++) out[i] = bits[i] ? '1' : '0';
    out[n] = '\0';
    return 1;
}

static int mark_bits(int mark, char *out, size_t cap) {
    uint8_t payload[1];

    payload[0] = (uint8_t)mark;
    return event_bits_from_payload(payload, 1, out, cap);
}

static int hist_bits_from_value(unsigned value,
                                size_t depth,
                                char *out,
                                size_t cap) {
    uint8_t payload[16];
    size_t i;

    if (depth > sizeof(payload)) return 0;
    for (i = 0; i < depth; i++) {
        size_t shift = depth - i - 1;
        payload[i] = (uint8_t)((value >> shift) & 1u);
    }
    return event_bits_from_payload(payload, depth, out, cap);
}

static int append_mark(char *out, size_t cap, size_t *off, int mark) {
    char bits[16];

    if (!mark_bits(mark, bits, sizeof(bits))) return 0;
    return append_text(out, cap, off, bits);
}

static int append_hist(char *out,
                       size_t cap,
                       size_t *off,
                       unsigned value,
                       size_t depth) {
    char bits[48];

    if (!hist_bits_from_value(value, depth, bits, sizeof(bits))) return 0;
    return append_text(out, cap, off, bits);
}

static int add_mark_tuple(ItemSet *out, int a, int b, int c, int arity) {
    char input[MAX_STR];
    size_t off = 0;

    input[0] = '\0';
    if (!append_mark(input, sizeof(input), &off, a)) return 0;
    if (!append_mark(input, sizeof(input), &off, b)) return 0;
    if (arity == 3 && !append_mark(input, sizeof(input), &off, c)) return 0;
    return itemset_add(out, input);
}

static int enum_mark_refl(int depth, ItemSet *out) {
    int m;

    itemset_init(out);
    for (m = 0; m <= 1; m++) {
        if (!add_mark_tuple(out, m, m, 0, 2)) return 0;
    }
    return 1;
}

static int enum_mark_symm(int depth, ItemSet *out) {
    int a;
    int b;

    itemset_init(out);
    for (a = 0; a <= 1; a++) {
        for (b = 0; b <= 1; b++) {
            if (!add_mark_tuple(out, a, b, 0, 2)) return 0;
        }
    }
    return 1;
}

static int enum_mark_trans(int depth, ItemSet *out) {
    int a;
    int b;
    int c;

    itemset_init(out);
    for (a = 0; a <= 1; a++) {
        for (b = 0; b <= 1; b++) {
            for (c = 0; c <= 1; c++) {
                if (!add_mark_tuple(out, a, b, c, 3)) return 0;
            }
        }
    }
    return 1;
}

static int enum_mark_no_confusion(int depth, ItemSet *out) {
    itemset_init(out);
    return add_mark_tuple(out, 0, 1, 0, 2) && add_mark_tuple(out, 1, 0, 0, 2);
}

static size_t hist_values_at_depth(size_t depth) {
    return ((size_t)1) << depth;
}

static int add_hist_pair(ItemSet *out,
                         unsigned a,
                         size_t a_depth,
                         unsigned b,
                         size_t b_depth) {
    char input[MAX_STR];
    size_t off = 0;

    input[0] = '\0';
    if (!append_hist(input, sizeof(input), &off, a, a_depth)) return 0;
    if (!append_hist(input, sizeof(input), &off, b, b_depth)) return 0;
    return itemset_add(out, input);
}

static int add_hist_triple(ItemSet *out,
                           unsigned a,
                           size_t a_depth,
                           unsigned b,
                           size_t b_depth,
                           unsigned c,
                           size_t c_depth) {
    char input[MAX_STR];
    size_t off = 0;

    input[0] = '\0';
    if (!append_hist(input, sizeof(input), &off, a, a_depth)) return 0;
    if (!append_hist(input, sizeof(input), &off, b, b_depth)) return 0;
    if (!append_hist(input, sizeof(input), &off, c, c_depth)) return 0;
    return itemset_add(out, input);
}

static int enum_hist_refl(int depth, ItemSet *out) {
    size_t d;

    itemset_init(out);
    for (d = 0; d <= (size_t)depth; d++) {
        unsigned v;
        for (v = 0; v < hist_values_at_depth(d); v++) {
            if (!add_hist_pair(out, v, d, v, d)) return 0;
        }
    }
    return 1;
}

static int enum_hist_symm(int depth, ItemSet *out) {
    size_t da;

    itemset_init(out);
    for (da = 0; da <= (size_t)depth; da++) {
        unsigned a;
        for (a = 0; a < hist_values_at_depth(da); a++) {
            size_t db;
            for (db = 0; db <= (size_t)depth; db++) {
                unsigned b;
                for (b = 0; b < hist_values_at_depth(db); b++) {
                    if (!add_hist_pair(out, a, da, b, db)) return 0;
                }
            }
        }
    }
    return 1;
}

static int enum_hist_trans(int depth, ItemSet *out) {
    size_t da;

    itemset_init(out);
    for (da = 0; da <= (size_t)depth; da++) {
        unsigned a;
        for (a = 0; a < hist_values_at_depth(da); a++) {
            size_t db;
            for (db = 0; db <= (size_t)depth; db++) {
                unsigned b;
                for (b = 0; b < hist_values_at_depth(db); b++) {
                    size_t dc;
                    for (dc = 0; dc <= (size_t)depth; dc++) {
                        unsigned c;
                        for (c = 0; c < hist_values_at_depth(dc); c++) {
                            if (!add_hist_triple(out, a, da, b, db, c, dc)) return 0;
                        }
                    }
                }
            }
        }
    }
    return 1;
}

static int enum_hist_empty_inversion(int depth, ItemSet *out) {
    size_t d;

    itemset_init(out);
    for (d = 0; d <= (size_t)depth; d++) {
        unsigned v;
        for (v = 0; v < hist_values_at_depth(d); v++) {
            if (!add_hist_pair(out, 0, 0, v, d)) return 0;
            if (!add_hist_pair(out, v, d, 0, 0)) return 0;
        }
    }
    return 1;
}

static int enum_hist_constructor_distinct(int depth, ItemSet *out) {
    size_t d;

    itemset_init(out);
    for (d = 0; d < (size_t)depth; d++) {
        unsigned tail;
        for (tail = 0; tail < hist_values_at_depth(d); tail++) {
            unsigned e0 = tail;
            unsigned e1 = (1u << d) | tail;
            if (!add_hist_pair(out, e0, d + 1, e1, d + 1)) return 0;
            if (!add_hist_pair(out, e1, d + 1, e0, d + 1)) return 0;
            if (!add_hist_pair(out, e0, d + 1, 0, 0)) return 0;
            if (!add_hist_pair(out, e1, d + 1, 0, 0)) return 0;
            if (!add_hist_pair(out, 0, 0, e0, d + 1)) return 0;
            if (!add_hist_pair(out, 0, 0, e1, d + 1)) return 0;
        }
    }
    return 1;
}

static int enum_ext_positive(int depth, ItemSet *out) {
    size_t d;

    itemset_init(out);
    for (d = 0; d <= (size_t)depth; d++) {
        unsigned h;
        for (h = 0; h < hist_values_at_depth(d); h++) {
            int m;
            for (m = 0; m <= 1; m++) {
                unsigned r = ((unsigned)m << d) | h;
                char input[MAX_STR];
                size_t off = 0;

                input[0] = '\0';
                if (!append_hist(input, sizeof(input), &off, h, d)) return 0;
                if (!append_mark(input, sizeof(input), &off, m)) return 0;
                if (!append_hist(input, sizeof(input), &off, r, d + 1)) return 0;
                if (!itemset_add(out, input)) return 0;
            }
        }
    }
    return 1;
}

static int append_result_value(unsigned h,
                               size_t h_depth,
                               unsigned k,
                               size_t k_depth,
                               unsigned *r,
                               size_t *r_depth) {
    *r_depth = h_depth + k_depth;
    if (*r_depth >= sizeof(unsigned) * 8) return 0;
    *r = (k << h_depth) | h;
    return 1;
}

static int enum_cont_positive(int depth, ItemSet *out) {
    size_t dh;

    itemset_init(out);
    for (dh = 0; dh <= (size_t)depth; dh++) {
        unsigned h;
        for (h = 0; h < hist_values_at_depth(dh); h++) {
            size_t dk;
            for (dk = 0; dk <= (size_t)depth; dk++) {
                unsigned k;
                for (k = 0; k < hist_values_at_depth(dk); k++) {
                    unsigned r;
                    size_t dr;
                    if (!append_result_value(h, dh, k, dk, &r, &dr)) return 0;
                    if (!add_hist_triple(out, h, dh, k, dk, r, dr)) return 0;
                }
            }
        }
    }
    return 1;
}

static int enum_unary_histories(int depth, ItemSet *out) {
    size_t d;

    itemset_init(out);
    for (d = 0; d <= (size_t)depth; d++) {
        unsigned v;
        for (v = 0; v < hist_values_at_depth(d); v++) {
            char input[MAX_STR];
            size_t off = 0;

            input[0] = '\0';
            if (!append_hist(input, sizeof(input), &off, v, d)) return 0;
            if (!itemset_add(out, input)) return 0;
        }
    }
    return 1;
}

static int append_probe(char *out, size_t cap, size_t *off, size_t probe) {
    uint8_t payload[16];
    size_t i;
    char bits[48];

    if (probe + 1 > sizeof(payload)) return 0;
    for (i = 0; i < probe; i++) payload[i] = 0;
    payload[probe] = 1;
    if (!event_bits_from_payload(payload, probe + 1, bits, sizeof(bits))) return 0;
    return append_text(out, cap, off, bits);
}

static int enum_ask_fixture(int depth, ItemSet *out) {
    size_t probe;

    itemset_init(out);
    for (probe = 0; probe <= (size_t)depth; probe++) {
        size_t hd;
        for (hd = 0; hd <= (size_t)depth; hd++) {
            unsigned h;
            for (h = 0; h < hist_values_at_depth(hd); h++) {
                int mark;
                for (mark = 0; mark <= 1; mark++) {
                    int evidence;
                    for (evidence = 0; evidence <= 1; evidence++) {
                        char input[MAX_STR];
                        size_t off = 0;

                        input[0] = '\0';
                        if (!append_probe(input, sizeof(input), &off, probe)) return 0;
                        if (!append_hist(input, sizeof(input), &off, h, hd)) return 0;
                        if (!append_mark(input, sizeof(input), &off, mark)) return 0;
                        if (!append_mark(input, sizeof(input), &off, evidence)) return 0;
                        if (!itemset_add(out, input)) return 0;
                    }
                }
            }
        }
    }
    return 1;
}

static int append_bundle_end(char *out, size_t cap, size_t *off) {
    uint8_t payload[2];
    char bits[24];

    payload[0] = 1;
    payload[1] = 1;
    if (!event_bits_from_payload(payload, 2, bits, sizeof(bits))) return 0;
    return append_text(out, cap, off, bits);
}

static int append_bundle(char *out,
                         size_t cap,
                         size_t *off,
                         unsigned value,
                         size_t len) {
    size_t i;

    for (i = 0; i < len; i++) {
        size_t shift = len - i - 1;
        size_t probe = (size_t)((value >> shift) & 1u);
        if (!append_probe(out, cap, off, probe)) return 0;
    }
    return append_bundle_end(out, cap, off);
}

static int enum_sigrel_fixture(int depth, ItemSet *out) {
    size_t blen;

    itemset_init(out);
    for (blen = 0; blen <= (size_t)depth; blen++) {
        unsigned b;
        for (b = 0; b < hist_values_at_depth(blen); b++) {
            size_t hd;
            for (hd = 0; hd <= (size_t)depth; hd++) {
                unsigned h;
                for (h = 0; h < hist_values_at_depth(hd); h++) {
                    size_t rd;
                    for (rd = 0; rd <= (size_t)depth; rd++) {
                        unsigned r;
                        for (r = 0; r < hist_values_at_depth(rd); r++) {
                            char input[MAX_STR];
                            size_t off = 0;

                            input[0] = '\0';
                            if (!append_bundle(input, sizeof(input), &off, b, blen)) return 0;
                            if (!append_hist(input, sizeof(input), &off, h, hd)) return 0;
                            if (!append_hist(input, sizeof(input), &off, r, rd)) return 0;
                            if (!itemset_add(out, input)) return 0;
                        }
                    }
                }
            }
        }
    }
    return 1;
}

static int enum_samesig_fixture(int depth, ItemSet *out) {
    return enum_sigrel_fixture(depth, out);
}

static int enum_ground_bhist_pairs(int depth, ItemSet *out) {
    return enum_hist_symm(depth, out);
}

static int enum_ground_flows(int depth, ItemSet *out) {
    uint8_t empty_payload[1];
    char empty_event[8];
    char b0[8];
    char b1[8];
    char pair[MAX_STR];

    (void)depth;
    itemset_init(out);
    empty_payload[0] = 0;
    if (!event_bits_from_payload(empty_payload, 0, empty_event, sizeof(empty_event))) return 0;
    if (!mark_bits(0, b0, sizeof(b0))) return 0;
    if (!mark_bits(1, b1, sizeof(b1))) return 0;
    if (!itemset_add(out, "")) return 0;
    if (!itemset_add(out, empty_event)) return 0;
    pair[0] = '\0';
    strcat(pair, b0);
    strcat(pair, b1);
    if (!itemset_add(out, pair)) return 0;
    return 1;
}

static int enum_ground_reject_reasons(int depth, ItemSet *out) {
    (void)depth;
    itemset_init(out);
    return itemset_add(out, "1") &&
           itemset_add(out, "010") &&
           itemset_add(out, "01x11") &&
           itemset_add(out, "") &&
           itemset_add(out, "00011") &&
           itemset_add(out, "01011_");
}

static const AuditTarget AUDIT_TARGETS[] = {
    { "BMark", "msame_refl", "manifests/mark/msame_refl.enum.ct", 1,
      "BMark is nullary; depth 1 is the whole closure.", enum_mark_refl },
    { "BMark", "msame_symm", "manifests/mark/msame_symm.enum.ct", 1,
      "All ordered BMark pairs are finite at depth 1.", enum_mark_symm },
    { "BMark", "msame_trans", "manifests/mark/msame_trans.enum.ct", 1,
      "All ordered BMark triples are finite at depth 1.", enum_mark_trans },
    { "BMark", "msame_no_confusion", "manifests/mark/msame_no_confusion.enum.ct", 1,
      "Only cross-constructor BMark pairs inhabit this slice.", enum_mark_no_confusion },

    { "BHist", "hsame_refl", "manifests/hist/hsame_refl.enum.ct", 1,
      "BHist is recursive; depth 1 is the first nontrivial finite slice.", enum_hist_refl },
    { "BHist", "hsame_symm", "manifests/hist/hsame_symm.enum.ct", 1,
      "Ordered pairs over BHist depth 1 give the first symmetry slice.", enum_hist_symm },
    { "BHist", "hsame_trans", "manifests/hist/hsame_trans.enum.ct", 1,
      "Ordered triples over BHist depth 1 keep the transitivity slice finite.", enum_hist_trans },
    { "BHist", "hsame_empty_inversion", "manifests/hist/hsame_empty_inversion.enum.ct", 1,
      "Empty-vs-depth-1 covers both constructor directions without exponential growth.", enum_hist_empty_inversion },
    { "BHist", "hsame_constructor_distinct", "manifests/hist/hsame_constructor_distinct.enum.ct", 1,
      "Depth 1 enumerates the outer-constructor disjointness boundary.", enum_hist_constructor_distinct },

    { "Ext", "ext_step", "manifests/ext/ext_step.enum.ct", 1,
      "Ext extends each source by one mark; source depth 1 is the first recursive slice.", enum_ext_positive },
    { "SigRel", "sigrel_basic", "manifests/sig/sigrel_basic.enum.ct", 1,
      "Fixture bundles, histories, and results are bounded to depth 1.", enum_sigrel_fixture },
    { "SameSig", "samesig_equiv", "manifests/sig/samesig_equiv.enum.ct", 1,
      "SameSig uses the same finite fixture slice as SigRel.", enum_samesig_fixture },
    { "Cont", "cont_basic", "manifests/cont/cont_basic.enum.ct", 1,
      "Continuation closure over both inputs at depth 1 gives exact positive append witnesses.", enum_cont_positive },
    { "Unary", "unary_basic", "manifests/unary/unary_basic.enum.ct", 2,
      "Unary is a BHist predicate; depth 2 is the first mixed positive/negative slice.", enum_unary_histories },
    { "Ask", "ask_basic", "manifests/ask/ask_basic.enum.ct", 1,
      "The executable Ask fixture is bounded by probe and history depth 1.", enum_ask_fixture },
    { "ExternalBinary", "external_binary_basic", "manifests/external_binary/external_binary_basic.enum.ct", 1,
      "ExternalBinary reuses BHist append; depth 1 mirrors the Cont slice.", enum_cont_positive },

    { "GroundCompiler", "flow_round_trip", "manifests/ground_compiler/flow_round_trip.enum.ct", 1,
      "The channel slice contains empty flow, empty event, and the two-mark flow.", enum_ground_flows },
    { "GroundCompiler", "bhist_injectivity", "manifests/ground_compiler/bhist_injectivity.enum.ct", 1,
      "BHist injectivity is checked on all depth-1 ordered pairs.", enum_ground_bhist_pairs },
    { "GroundCompiler", "reject_reasons", "manifests/ground_compiler/reject_reasons.enum.ct", 1,
      "Reject taxonomy is a closed six-case decoder fixture.", enum_ground_reject_reasons }
};

static size_t count_covered(const ItemSet *enumerated, const ItemSet *manifest) {
    size_t covered = 0;
    size_t i;

    for (i = 0; i < enumerated->count; i++) {
        if (itemset_contains(manifest, enumerated->items[i].text)) covered++;
    }
    return covered;
}

static void print_gaps(const ItemSet *enumerated, const ItemSet *manifest) {
    size_t i;
    size_t printed = 0;
    size_t missing = 0;

    for (i = 0; i < enumerated->count; i++) {
        if (!itemset_contains(manifest, enumerated->items[i].text)) {
            missing++;
            if (printed < MAX_GAPS_PRINTED) {
                printf("    - %s\n", enumerated->items[i].text[0] ? enumerated->items[i].text : "<empty>");
                printed++;
            }
        }
    }
    if (missing > printed) {
        printf("    ... %zu more gap(s)\n", missing - printed);
    }
}

int main(int argc, char **argv) {
    int strict = 0;
    size_t target_count = sizeof(AUDIT_TARGETS) / sizeof(AUDIT_TARGETS[0]);
    size_t pass_count = 0;
    size_t partial_count = 0;
    size_t parse_fail_count = 0;
    size_t i;

    if (argc > 1 && strcmp(argv[1], "--strict") == 0) strict = 1;

    printf("== manifest_exhaustiveness_audit ==\n");

    for (i = 0; i < target_count; i++) {
        const AuditTarget *target = &AUDIT_TARGETS[i];
        ItemSet enumerated;
        ItemSet manifest;
        size_t manifest_raw_count = 0;
        size_t covered;
        double percent;

        printf("\nTarget: %s / %s\n", target->type_name, target->theorem_name);
        printf("  manifest: %s\n", target->manifest_path);
        printf("  closure depth %d: %s\n", target->closure_depth, target->depth_note);

        if (!target->enumerate(target->closure_depth, &enumerated)) {
            printf("  enumerate: FAIL\n");
            parse_fail_count++;
            continue;
        }
        printf("  closure instances: %zu\n", enumerated.count);

        if (!parse_manifest_inputs(target->manifest_path, &manifest, &manifest_raw_count)) {
            printf("  manifest parse: FAIL\n");
            parse_fail_count++;
            continue;
        }
        printf("  manifest cases: %zu raw, %zu unique inputs\n",
               manifest_raw_count,
               manifest.count);

        covered = count_covered(&enumerated, &manifest);
        percent = enumerated.count == 0
            ? 100.0
            : (100.0 * (double)covered / (double)enumerated.count);
        printf("  Exhaustiveness: %zu/%zu (%.1f%%)\n",
               covered,
               enumerated.count,
               percent);

        if (covered == enumerated.count) {
            printf("  status: PASS\n");
            pass_count++;
        } else {
            printf("  status: PARTIAL\n");
            printf("  GAPS (instances in closure but not in manifest):\n");
            print_gaps(&enumerated, &manifest);
            partial_count++;
        }
    }

    printf("\nSummary: %zu audit targets, %zu strict PASS, %zu partial coverage, %zu parse/enumeration failure\n",
           target_count,
           pass_count,
           partial_count,
           parse_fail_count);

    if (strict && (partial_count != 0 || parse_fail_count != 0)) return 1;
    return parse_fail_count == 0 ? 0 : 1;
}
