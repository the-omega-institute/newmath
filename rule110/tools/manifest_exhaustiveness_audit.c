#include "groundcompiler_encoding.h"

#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_INSTANCES 16
#define MAX_CASES 64
#define MAX_LINE 1024
#define MAX_BITS 512
#define BMARK_DEPTH 3

typedef struct BMarkNode {
    int constructor_id;
    int n_children;
} BMarkNode;

typedef struct {
    BMarkNode value;
} ManifestCase;

static void init_bmark(BMarkNode *node, int constructor_id) {
    node->constructor_id = constructor_id;
    node->n_children = 0;
}

static int bmark_equal(const BMarkNode *a, const BMarkNode *b) {
    return a->constructor_id == b->constructor_id && a->n_children == b->n_children;
}

static const char *bmark_name(const BMarkNode *node) {
    if (node->constructor_id == 0) return "b0";
    if (node->constructor_id == 1) return "b1";
    return "unknown";
}

static size_t enumerate_bmark(int max_depth, BMarkNode *out_list, size_t cap) {
    size_t count = 0;

    if (max_depth < 0 || cap < 2) return 0;

    init_bmark(&out_list[count++], 0);
    init_bmark(&out_list[count++], 1);

    return count;
}

static int bits_from_string(const char *s, uint8_t *out, size_t cap, size_t *out_len) {
    size_t len = 0;

    while (*s == '0' || *s == '1') {
        if (len >= cap) return 0;
        out[len++] = (uint8_t)(*s == '1');
        s++;
    }

    *out_len = len;
    return len > 0;
}

static int decode_bmark_event(const uint8_t *bits,
                              size_t bits_len,
                              size_t *offset,
                              BMarkNode *out) {
    GcDecResult decoded;

    decoded = gc_dec_event(bits + *offset, bits_len - *offset, bits_len + 1);
    if (decoded.status != GC_OK) {
        free(decoded.event);
        return 0;
    }
    if (decoded.event_len != 1) {
        free(decoded.event);
        return 0;
    }
    if (decoded.event[0] == 0) {
        init_bmark(out, 0);
    } else if (decoded.event[0] == 1) {
        init_bmark(out, 1);
    } else {
        free(decoded.event);
        return 0;
    }

    *offset += decoded.bytes_consumed;
    free(decoded.event);
    return 1;
}

static int parse_msame_input(const char *input_bits, BMarkNode *out) {
    uint8_t bits[MAX_BITS];
    size_t bits_len;
    size_t offset = 0;
    BMarkNode left;
    BMarkNode right;

    if (!bits_from_string(input_bits, bits, sizeof(bits), &bits_len)) return 0;
    if (!decode_bmark_event(bits, bits_len, &offset, &left)) return 0;
    if (!decode_bmark_event(bits, bits_len, &offset, &right)) return 0;
    if (offset != bits_len) return 0;
    if (!bmark_equal(&left, &right)) return 0;

    *out = left;
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

static int parse_msame_refl_manifest(const char *path, ManifestCase *out, size_t cap) {
    FILE *f;
    char line[MAX_LINE];
    size_t count = 0;

    f = fopen(path, "r");
    if (!f) return -1;

    while (fgets(line, sizeof(line), f)) {
        char *trimmed = trim_ascii(line);
        char *input;
        char *end;
        BMarkNode value;

        if (strncmp(trimmed, "case ", 5) != 0) continue;

        input = strstr(trimmed, "input=");
        if (!input) {
            fclose(f);
            return -1;
        }
        input += 6;
        end = input;
        while (*end == '0' || *end == '1') end++;
        if (end == input) {
            fclose(f);
            return -1;
        }
        *end = '\0';

        if (!parse_msame_input(input, &value)) {
            fclose(f);
            return -1;
        }
        if (count >= cap) {
            fclose(f);
            return -1;
        }
        out[count].value = value;
        count++;
    }

    fclose(f);
    return (int)count;
}

static int manifest_contains(const ManifestCase *cases,
                             size_t case_count,
                             const BMarkNode *value) {
    size_t i;

    for (i = 0; i < case_count; i++) {
        if (bmark_equal(&cases[i].value, value)) return 1;
    }
    return 0;
}

static size_t count_coverage(const BMarkNode *enumerated,
                             size_t enumerated_count,
                             const ManifestCase *cases,
                             size_t case_count) {
    size_t covered = 0;
    size_t i;

    for (i = 0; i < enumerated_count; i++) {
        if (manifest_contains(cases, case_count, &enumerated[i])) covered++;
    }
    return covered;
}

static void list_gaps(const BMarkNode *enumerated,
                      size_t enumerated_count,
                      const ManifestCase *cases,
                      size_t case_count) {
    size_t i;

    for (i = 0; i < enumerated_count; i++) {
        if (!manifest_contains(cases, case_count, &enumerated[i])) {
            printf("    - %s\n", bmark_name(&enumerated[i]));
        }
    }
}

int main(int argc, char **argv) {
    const char *manifest_path = "manifests/mark/msame_refl.enum.ct";
    int strict = 0;
    BMarkNode enumerated[MAX_INSTANCES];
    ManifestCase cases[MAX_CASES];
    size_t e_count;
    int parsed;
    size_t c_count;
    size_t covered;
    double percent;

    if (argc > 1 && strcmp(argv[1], "--strict") == 0) strict = 1;

    printf("== manifest_exhaustiveness_audit ==\n");
    printf("Target: BMark / msame_refl (lean4/BEDC/FKernel/Mark.lean::msame_refl)\n");
    printf("Manifest: rule110/manifests/mark/msame_refl.enum.ct\n");

    e_count = enumerate_bmark(BMARK_DEPTH, enumerated, MAX_INSTANCES);
    printf("  BMark closure enumerated to depth %d: %zu instances\n", BMARK_DEPTH, e_count);

    parsed = parse_msame_refl_manifest(manifest_path, cases, MAX_CASES);
    if (parsed < 0) {
        printf("  Manifest parse: FAIL\n");
        return strict ? 1 : 0;
    }
    c_count = (size_t)parsed;
    printf("  Manifest case count: %zu\n", c_count);

    covered = count_coverage(enumerated, e_count, cases, c_count);
    percent = e_count == 0 ? 100.0 : (100.0 * (double)covered / (double)e_count);
    printf("  Exhaustiveness: %zu/%zu (%.1f%%)\n", covered, e_count, percent);

    if (covered < e_count) {
        printf("  GAPS (instances in closure but not in manifest):\n");
        list_gaps(enumerated, e_count, cases, c_count);
    }

    if (covered == e_count) {
        printf("ALL exhaustiveness audit passed for depth %d\n", BMARK_DEPTH);
        return 0;
    }

    printf("FAIL %zu missing instance(s)\n", e_count - covered);
    return strict ? 1 : 0;
}
