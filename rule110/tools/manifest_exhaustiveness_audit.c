#include "groundcompiler_encoding.h"

#include <ctype.h>
#include <stdbool.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_ITEMS 4096
#define MAX_STR 512
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
    bool finite_witness_convention;
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

static int append_event_payload(char *out,
                                size_t cap,
                                size_t *off,
                                const uint8_t *payload,
                                size_t payload_len) {
    char bits[MAX_STR];

    if (!event_bits_from_payload(payload, payload_len, bits, sizeof(bits))) return 0;
    return append_text(out, cap, off, bits);
}

static int append_fold_tag(char *out, size_t cap, size_t *off, size_t tag) {
    uint8_t payload[16];
    size_t i;

    if (tag + 1 > sizeof(payload)) return 0;
    for (i = 0; i < tag; i++) payload[i] = 1;
    payload[tag] = 0;
    return append_event_payload(out, cap, off, payload, tag + 1);
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

static int add_hist_tuple4(ItemSet *out,
                           unsigned a,
                           size_t da,
                           unsigned b,
                           size_t db,
                           unsigned c,
                           size_t dc,
                           unsigned d,
                           size_t dd) {
    char input[MAX_STR];
    size_t off = 0;

    input[0] = '\0';
    if (!append_hist(input, sizeof(input), &off, a, da)) return 0;
    if (!append_hist(input, sizeof(input), &off, b, db)) return 0;
    if (!append_hist(input, sizeof(input), &off, c, dc)) return 0;
    if (!append_hist(input, sizeof(input), &off, d, dd)) return 0;
    return itemset_add(out, input);
}

static int add_hist_tuple5(ItemSet *out,
                           unsigned a,
                           size_t da,
                           unsigned b,
                           size_t db,
                           unsigned c,
                           size_t dc,
                           unsigned d,
                           size_t dd,
                           unsigned e,
                           size_t de) {
    char input[MAX_STR];
    size_t off = 0;

    input[0] = '\0';
    if (!append_hist(input, sizeof(input), &off, a, da)) return 0;
    if (!append_hist(input, sizeof(input), &off, b, db)) return 0;
    if (!append_hist(input, sizeof(input), &off, c, dc)) return 0;
    if (!append_hist(input, sizeof(input), &off, d, dd)) return 0;
    if (!append_hist(input, sizeof(input), &off, e, de)) return 0;
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

static int append_bhist_bundle(char *out,
                               size_t cap,
                               size_t *off,
                               unsigned value,
                               size_t len,
                               size_t item_depth) {
    size_t i;

    for (i = 0; i < len; i++) {
        size_t shift = item_depth * (len - i - 1);
        unsigned mask = item_depth == 0 ? 0u : ((1u << item_depth) - 1u);
        unsigned item = (value >> shift) & mask;
        if (!append_hist(out, cap, off, item, item_depth)) return 0;
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

static int enum_modn_rows(int depth, ItemSet *out) {
    size_t d;

    itemset_init(out);
    for (d = 0; d <= (size_t)depth; d++) {
        unsigned modulus = d == 0 ? 0u : (((unsigned)1 << d) - 1u);
        if (!add_hist_tuple4(out, modulus, d, 0, 0, 0, 0, 0, 0)) return 0;
    }
    return 1;
}

static int enum_modn_operations(int depth, ItemSet *out) {
    size_t d;

    itemset_init(out);
    for (d = 0; d <= (size_t)depth; d++) {
        unsigned modulus = d == 0 ? 0u : (((unsigned)1 << d) - 1u);
        if (!add_hist_tuple5(out, modulus, d, 0, 0, 0, 0, 0, 0, 0, 0)) return 0;
    }
    return 1;
}

static int enum_s1_e1_component_rows(int depth, ItemSet *out) {
    size_t ddx;

    itemset_init(out);
    for (ddx = 0; ddx <= (size_t)depth; ddx++) {
        unsigned dx;
        for (dx = 0; dx < hist_values_at_depth(ddx); dx++) {
            size_t ddy;
            for (ddy = 0; ddy <= (size_t)depth; ddy++) {
                unsigned dy;
                for (dy = 0; dy < hist_values_at_depth(ddy); dy++) {
                    unsigned x = ((unsigned)1 << ddx) | dx;
                    size_t dx1 = ddx + 1;
                    unsigned y = ((unsigned)1 << ddy) | dy;
                    size_t dy1 = ddy + 1;
                    unsigned tail;
                    size_t tail_depth;
                    unsigned point;

                    if (!append_result_value(x, dx1, dy, ddy, &tail, &tail_depth)) return 0;
                    point = ((unsigned)1 << tail_depth) | tail;
                    if (!add_hist_tuple5(out, x, dx1, y, dy1, 3, 2, point,
                                         tail_depth + 1, tail, tail_depth)) return 0;
                }
            }
        }
    }
    return 1;
}

static int append_fold_flow_with_window(char *input,
                                        size_t cap,
                                        size_t *off,
                                        unsigned window,
                                        size_t window_depth) {
    size_t i;

    for (i = 0; i < 9; i++) {
        if (!append_fold_tag(input, cap, off, i)) return 0;
        if (i == 0) {
            if (!append_hist(input, cap, off, window, window_depth)) return 0;
        } else {
            if (!append_hist(input, cap, off, 0, 0)) return 0;
        }
    }
    return 1;
}

static int enum_fold_window_flows(int depth, ItemSet *out) {
    size_t d;

    itemset_init(out);
    for (d = 0; d <= (size_t)depth; d++) {
        unsigned window;
        for (window = 0; window < hist_values_at_depth(d); window++) {
            char input[MAX_STR];
            size_t off = 0;

            input[0] = '\0';
            if (!append_fold_flow_with_window(input, sizeof(input), &off, window, d)) return 0;
            if (!itemset_add(out, input)) return 0;
        }
    }
    return 1;
}

static int enum_fold_window_flow_pairs(int depth, ItemSet *out) {
    size_t d;

    itemset_init(out);
    for (d = 0; d <= (size_t)depth; d++) {
        unsigned window;
        for (window = 0; window < hist_values_at_depth(d); window++) {
            char input[MAX_STR];
            size_t off = 0;

            input[0] = '\0';
            if (!append_fold_flow_with_window(input, sizeof(input), &off, 0, 0)) return 0;
            if (!append_fold_flow_with_window(input, sizeof(input), &off, window, d)) return 0;
            if (!itemset_add(out, input)) return 0;
        }
    }
    return 1;
}

static int enum_atom_infer_fixture(int depth, ItemSet *out) {
    int ctx;

    itemset_init(out);
    for (ctx = 0; ctx <= depth; ctx++) {
        uint8_t ctx_payload[16];
        char ctx_bits[MAX_STR];
        int i;

        if (ctx > (int)sizeof(ctx_payload)) return 0;
        for (i = 0; i < ctx; i++) ctx_payload[i] = 0;
        if (!event_bits_from_payload(ctx_payload, (size_t)ctx, ctx_bits, sizeof(ctx_bits))) return 0;

        {
            uint8_t sort_payload[1];
            char atom_bits[MAX_STR];
            char input[MAX_STR];
            size_t off = 0;

            sort_payload[0] = 0;
            if (!event_bits_from_payload(sort_payload, 1, atom_bits, sizeof(atom_bits))) return 0;
            input[0] = '\0';
            if (!append_text(input, sizeof(input), &off, ctx_bits)) return 0;
            if (!append_text(input, sizeof(input), &off, atom_bits)) return 0;
            if (!itemset_add(out, input)) return 0;
        }

        for (i = 0; i <= depth; i++) {
            uint8_t var_payload[16];
            char atom_bits[MAX_STR];
            char input[MAX_STR];
            size_t off = 0;
            int j;

            if (i + 1 > (int)sizeof(var_payload)) return 0;
            var_payload[0] = 1;
            for (j = 1; j <= i; j++) var_payload[j] = 0;
            if (!event_bits_from_payload(var_payload, (size_t)i + 1, atom_bits,
                                         sizeof(atom_bits))) return 0;
            input[0] = '\0';
            if (!append_text(input, sizeof(input), &off, ctx_bits)) return 0;
            if (!append_text(input, sizeof(input), &off, atom_bits)) return 0;
            if (!itemset_add(out, input)) return 0;
        }
    }
    return 1;
}

static int enum_nat_bhist_single_rows(int depth, ItemSet *out) {
    int d;

    itemset_init(out);
    for (d = 0; d <= depth; d++) {
        char input[MAX_STR];
        size_t off = 0;

        input[0] = '\0';
        if (!append_hist(input, sizeof(input), &off, 0, (size_t)d)) return 0;
        if (!itemset_add(out, input)) return 0;
    }
    return 1;
}

static int enum_bhist_term_embedding_rows(int depth, ItemSet *out) {
    size_t d;

    itemset_init(out);
    for (d = 0; d <= (size_t)depth; d++) {
        unsigned h;
        for (h = 0; h < hist_values_at_depth(d); h++) {
            char input[MAX_STR];
            size_t off = 0;

            input[0] = '\0';
            if (!append_hist(input, sizeof(input), &off, h, d)) return 0;
            if (!itemset_add(out, input)) return 0;
        }
    }
    for (d = 0; d <= (size_t)depth; d++) {
        unsigned h;
        for (h = 0; h < hist_values_at_depth(d); h++) {
            size_t dk;
            for (dk = 0; dk <= (size_t)depth; dk++) {
                unsigned k;
                for (k = 0; k < hist_values_at_depth(dk); k++) {
                    if (!add_hist_pair(out, h, d, k, dk)) return 0;
                }
            }
        }
    }
    return 1;
}

static int enum_topology_bundle_rows(int depth, ItemSet *out) {
    size_t left_len;

    itemset_init(out);
    for (left_len = 0; left_len <= 1; left_len++) {
        unsigned left_count = left_len == 0 ? 1u : (unsigned)hist_values_at_depth((size_t)depth);
        unsigned left;
        for (left = 0; left < left_count; left++) {
            size_t right_len;
            for (right_len = 0; right_len <= 1; right_len++) {
                unsigned right_count = right_len == 0 ? 1u : (unsigned)hist_values_at_depth((size_t)depth);
                unsigned right;
                for (right = 0; right < right_count; right++) {
                    unsigned point;
                    for (point = 0; point < hist_values_at_depth((size_t)depth); point++) {
                        char input[MAX_STR];
                        size_t off = 0;

                        input[0] = '\0';
                        if (!append_bhist_bundle(input, sizeof(input), &off, left,
                                                 left_len, (size_t)depth)) return 0;
                        if (!append_bhist_bundle(input, sizeof(input), &off, right,
                                                 right_len, (size_t)depth)) return 0;
                        if (!append_hist(input, sizeof(input), &off, point,
                                         (size_t)depth)) return 0;
                        if (!itemset_add(out, input)) return 0;
                    }
                }
            }
        }
    }
    return 1;
}

static int enum_topology_ledger_tags(int depth, ItemSet *out) {
    static const unsigned tag_values[] = { 0u, 0u, 1u, 0u, 1u, 2u };
    static const size_t tag_depths[] = { 0u, 1u, 1u, 2u, 2u, 2u };
    size_t i;

    (void)depth;
    itemset_init(out);
    for (i = 0; i < 6; i++) {
        if (!add_hist_triple(out, tag_values[i], tag_depths[i],
                             tag_values[i], tag_depths[i], 0, 0)) return 0;
    }
    for (i = 0; i < 6; i++) {
        size_t j;
        for (j = i + 1; j < 6; j++) {
            if (!add_hist_triple(out, tag_values[i], tag_depths[i],
                                 tag_values[j], tag_depths[j], 0, 0)) return 0;
        }
    }
    return 1;
}

static const AuditTarget AUDIT_TARGETS[] = {
    { "BMark", "msame_refl", "manifests/mark/msame_refl.enum.ct", 1,
      "BMark is nullary; depth 1 is the whole closure.", false, enum_mark_refl },
    { "BMark", "msame_symm", "manifests/mark/msame_symm.enum.ct", 1,
      "All ordered BMark pairs are finite at depth 1.", false, enum_mark_symm },
    { "BMark", "msame_trans", "manifests/mark/msame_trans.enum.ct", 1,
      "All ordered BMark triples are finite at depth 1.", false, enum_mark_trans },
    { "BMark", "msame_no_confusion", "manifests/mark/msame_no_confusion.enum.ct", 1,
      "Only cross-constructor BMark pairs inhabit this slice.", false, enum_mark_no_confusion },

    { "BHist", "hsame_refl", "manifests/hist/hsame_refl.enum.ct", 1,
      "BHist is recursive; depth 1 is the first nontrivial finite slice.", false, enum_hist_refl },
    /* Decision A: BHist is Empty/e0/e1 and hsame is Eq; the depth-1 pair slice is 9 cases. */
    { "BHist", "hsame_symm", "manifests/hist/hsame_symm.enum.ct", 1,
      "Ordered pairs over BHist depth 1 give the first symmetry slice.", false, enum_hist_symm },
    /* Decision C: BHist is Empty/e0/e1 recursive; depth-1 triples are 27 cases and the manifest records 8 representatives. */
    { "BHist", "hsame_trans", "manifests/hist/hsame_trans.enum.ct", 1,
      "Convention bound: BHist transitivity triples grow as the finite recursive slice expands.", true, enum_hist_trans },
    { "BHist", "hsame_empty_inversion", "manifests/hist/hsame_empty_inversion.enum.ct", 1,
      "Empty-vs-depth-1 covers both constructor directions without exponential growth.", false, enum_hist_empty_inversion },
    { "BHist", "hsame_constructor_distinct", "manifests/hist/hsame_constructor_distinct.enum.ct", 1,
      "Depth 1 enumerates the outer-constructor disjointness boundary.", false, enum_hist_constructor_distinct },

    /* Decision A: Ext has constructors Ext.e0 and Ext.e1; the depth-1 positive closure has 6 cases. */
    { "Ext", "ext_step", "manifests/ext/ext_step.enum.ct", 1,
      "Ext extends each source by one mark; source depth 1 is the first recursive slice.", false, enum_ext_positive },
    /* Decision C: SigRel recurses over ProbeBundle and abstract AskSetup; depth-1 fixture closure has 27 triples. */
    { "SigRel", "sigrel_basic", "manifests/sig/sigrel_basic.enum.ct", 1,
      "Convention bound: SigRel fixtures are semantic Ask examples, not exhaustive bundle/history/result triples.", true, enum_sigrel_fixture },
    /* Decision C: SameSig is defined through two SigRel witnesses; depth-1 fixture closure has 27 triples. */
    { "SameSig", "samesig_equiv", "manifests/sig/samesig_equiv.enum.ct", 1,
      "Convention bound: SameSig fixtures cover equivalence representatives, not the full SigRel-derived slice.", true, enum_samesig_fixture },
    /* Decision A: Cont is r = append h k over BHist; the depth-1 positive closure has 9 cases. */
    { "Cont", "cont_basic", "manifests/cont/cont_basic.enum.ct", 1,
      "Continuation closure over both inputs at depth 1 gives exact positive append witnesses.", false, enum_cont_positive },
    /* Decision A: UnaryHistory accepts Empty/e1 tails and rejects e0 tails; the depth-2 unary-history slice has 7 cases. */
    { "Unary", "unary_basic", "manifests/unary/unary_basic.enum.ct", 2,
      "Unary is a BHist predicate; depth 2 is the first mixed positive/negative slice.", false, enum_unary_histories },
    /* Decision C: AskSetup has abstract ProbeName and Evidence carriers; the executable depth-1 fixture has 24 tuples. */
    { "Ask", "ask_basic", "manifests/ask/ask_basic.enum.ct", 1,
      "Convention bound: Ask fixtures show selected policy witnesses, not every probe/history/mark/evidence tuple.", true, enum_ask_fixture },
    /* Decision A: ExternalBinary aliases BWord to BHist and reuses Cont.append; the depth-1 closure has 9 cases. */
    { "ExternalBinary", "external_binary_basic", "manifests/external_binary/external_binary_basic.enum.ct", 1,
      "ExternalBinary reuses BHist append; depth 1 mirrors the Cont slice.", false, enum_cont_positive },

    { "GroundCompiler", "flow_round_trip", "manifests/ground_compiler/flow_round_trip.enum.ct", 1,
      "The channel slice contains empty flow, empty event, and the two-mark flow.", false, enum_ground_flows },
    /* Decision C: channel_encoding_bijection and legal_stream_completeness range over recursive BHist streams; the manifest keeps 6 representative rows against 9 depth-1 pairs. */
    { "GroundCompiler", "bhist_injectivity", "manifests/ground_compiler/bhist_injectivity.enum.ct", 1,
      "Convention bound: BHist injectivity fixtures keep representative stream pairs, not every depth-1 pair.", true, enum_ground_bhist_pairs },
    { "GroundCompiler", "reject_reasons", "manifests/ground_compiler/reject_reasons.enum.ct", 1,
      "Reject taxonomy is a closed six-case decoder fixture.", false, enum_ground_reject_reasons },

    { "CircleModN", "modn_classifier_concrete_rows", "manifests/circle_up/circle_modn_rows.enum.ct", 2,
      "Unary modulus depth 2 with singleton h/k/witness is an exact finite ModN classifier slice.", false, enum_modn_rows },
    { "CircleModN", "modn_singleton_operation_descent", "manifests/circle_up/circle_modn_operations.enum.ct", 2,
      "Unary modulus depth 2 with singleton operands and closed-form Empty operations.", false, enum_modn_operations },
    { "CircleS1", "s1_e1_components_carrier_exactness", "manifests/circle_up/circle_s1_rows.enum.ct", 1,
      "Convention bound: S1 e1-component rows range over recursive dx/dy tails; the manifest records selected positive component rows.", true, enum_s1_e1_component_rows },

    { "FoldMomentKernelUp", "fold_round_trip", "manifests/fold_up/fold_round_trip.enum.ct", 1,
      "Convention bound: the nine-field recursive product is represented by a depth-1 window-varying kernel slice.", true, enum_fold_window_flows },
    { "FoldMomentKernelUp", "fold_tag_layout", "manifests/fold_up/fold_tag_layout.enum.ct", 1,
      "Convention bound: tag layout is checked over the same depth-1 window-varying kernel slice.", true, enum_fold_window_flows },
    { "FoldMomentKernelUp", "fold_event_flow_injective", "manifests/fold_up/fold_injectivity.enum.ct", 1,
      "Convention bound: injectivity is checked over pairs with fixed left kernel and a depth-1 right window slice.", true, enum_fold_window_flow_pairs },

    { "MetaCICAtom", "inferAtom", "manifests/meta_cic/atom_infer.enum.ct", 3,
      "Convention bound: atom inference enumerates sort and var atoms over contexts up to length 3; the manifest keeps sound and rejecting representatives.", true, enum_atom_infer_fixture },
    { "MetaCICBHist", "bhistLen_natToBHist", "manifests/meta_cic/bhist_nat_len.enum.ct", 3,
      "natToBHist rows are exactly all-e0 histories through depth 3.", false, enum_nat_bhist_single_rows },
    { "MetaCICBHist", "bhistToTerm_injective", "manifests/meta_cic/bhist_term_embedding.enum.ct", 1,
      "Convention bound: closed rows and ordered depth-1 injectivity pairs share one mixed-shape manifest.", true, enum_bhist_term_embedding_rows },

    { "TopologyCarrier", "finite_base_append_decomposition", "manifests/topology_up/topology_finite_base_neighborhood.enum.ct", 1,
      "Convention bound: finite-base bundles are recursive; the audit uses left/right length at most 1 with depth-1 BHist items.", true, enum_topology_bundle_rows },
    { "TopologyCarrier", "finite_base_carrier_meet_scope", "manifests/topology_up/topology_carrier_rows.enum.ct", 1,
      "Convention bound: carrier rows use the same bounded bundle slice with representative ledgers.", true, enum_topology_bundle_rows },
    { "TopologyLedgerRow", "ledger_constructor_tags", "manifests/topology_up/topology_ledger_tags.enum.ct", 1,
      "Convention bound: six constructor tags are closed, while the no-confusion surface has fifteen unordered tag pairs.", true, enum_topology_ledger_tags }
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
    size_t convention_count = 0;
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
        } else if (target->finite_witness_convention) {
            printf("  status: CONVENTION BOUND\n");
            printf("  GAPS (instances outside the manifest convention slice):\n");
            print_gaps(&enumerated, &manifest);
            convention_count++;
        } else {
            printf("  status: PARTIAL\n");
            printf("  GAPS (instances in closure but not in manifest):\n");
            print_gaps(&enumerated, &manifest);
            partial_count++;
        }
    }

    printf("\nSummary: %zu audit targets, %zu strict PASS, %zu convention bound, %zu partial coverage, %zu parse/enumeration failure\n",
           target_count,
           pass_count,
           convention_count,
           partial_count,
           parse_fail_count);

    if (strict && (partial_count != 0 || parse_fail_count != 0)) return 1;
    return parse_fail_count == 0 ? 0 : 1;
}
