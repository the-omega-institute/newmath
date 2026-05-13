#include <ctype.h>
#include <dirent.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_LINE 8192
#define MAX_NAME 256
#define MAX_BITS 2048
#define MAX_PATH_TEXT 512

typedef struct {
    const char *label;
    size_t offset;
    size_t len;
    const char *color;
} Segment;

typedef struct {
    const char *id;
    const Segment *segments;
    size_t segment_count;
} CuratedLayers;

typedef struct {
    char case_name[MAX_NAME];
    char input[MAX_BITS];
    char initial[MAX_BITS];
    size_t payload_start;
    size_t payload_len;
} ManifestCase;

typedef struct {
    char module_dir[MAX_NAME];
    char module_name[MAX_NAME];
    char manifest_file[MAX_NAME];
    char manifest_stem[MAX_NAME];
    char source_manifest[MAX_PATH_TEXT];
    ManifestCase manifest_case;
    size_t evolution_steps;
} Operation;

typedef struct {
    Operation *items;
    size_t count;
    size_t cap;
} OperationList;

typedef struct {
    char names[128][MAX_NAME];
    size_t count;
} NameList;

static const Segment MSAME_SEGMENTS[] = {
    {"left mark b0", 0, 3, "#f2c14e"},
    {"right mark b0", 3, 3, "#4d9de0"}
};

static const Segment HSAME_SEGMENTS[] = {
    {"left empty BHist", 0, 2, "#f2c14e"},
    {"right empty BHist", 2, 2, "#4d9de0"}
};

static const Segment EXT_SEGMENTS[] = {
    {"source empty BHist", 0, 2, "#f2c14e"},
    {"mark b0", 2, 3, "#59a14f"},
    {"result e0 empty", 5, 3, "#e15759"}
};

static const Segment CONT_SEGMENTS[] = {
    {"left empty BHist", 0, 2, "#f2c14e"},
    {"right empty BHist", 2, 2, "#4d9de0"},
    {"append result empty", 4, 2, "#e15759"}
};

static const CuratedLayers CURATED[] = {
    {"mark__msame_refl__b0_b0", MSAME_SEGMENTS, sizeof(MSAME_SEGMENTS) / sizeof(MSAME_SEGMENTS[0])},
    {"hist__hsame_refl__empty", HSAME_SEGMENTS, sizeof(HSAME_SEGMENTS) / sizeof(HSAME_SEGMENTS[0])},
    {"ext__ext_step__empty_b0_e0_empty", EXT_SEGMENTS, sizeof(EXT_SEGMENTS) / sizeof(EXT_SEGMENTS[0])},
    {"cont__cont_basic__empty_empty_empty", CONT_SEGMENTS, sizeof(CONT_SEGMENTS) / sizeof(CONT_SEGMENTS[0])}
};

static const char *MODULE_DIRS[] = {
    "mark",
    "hist",
    "ext",
    "sig",
    "cont",
    "bundle",
    "unary",
    "ask",
    "external_binary",
    "gap",
    "package",
    "name_cert",
    "settled",
    "ground_compiler",
    "circle_up",
    "fold_up",
    "meta_cic",
    "topology_up"
};

static char *trim_ascii(char *s) {
    char *end;

    while (*s && isspace((unsigned char)*s)) s++;
    end = s + strlen(s);
    while (end > s && isspace((unsigned char)end[-1])) end--;
    *end = '\0';
    return s;
}

static int copy_text(char *dst, size_t dst_cap, const char *src) {
    size_t len = strlen(src);

    if (len + 1 > dst_cap) return 0;
    memcpy(dst, src, len + 1);
    return 1;
}

static int append_text(char *dst, size_t dst_cap, const char *src) {
    size_t dst_len = strlen(dst);
    size_t src_len = strlen(src);

    if (dst_len + src_len + 1 > dst_cap) return 0;
    memcpy(dst + dst_len, src, src_len + 1);
    return 1;
}

static int ends_with(const char *s, const char *suffix) {
    size_t slen = strlen(s);
    size_t tlen = strlen(suffix);

    return slen >= tlen && strcmp(s + slen - tlen, suffix) == 0;
}

static int parse_size_value(const char *s, size_t *out) {
    char *end = NULL;
    unsigned long value = strtoul(s, &end, 10);

    if (end == s) return 0;
    while (*end && isspace((unsigned char)*end)) end++;
    if (*end != '\0') return 0;
    *out = (size_t)value;
    return 1;
}

static int parse_field(const char *line,
                       const char *key,
                       char *out,
                       size_t out_cap) {
    const char *start = strstr(line, key);
    const char *end;
    size_t len;

    if (start == NULL) return 0;
    start += strlen(key);
    end = strchr(start, ';');
    if (end == NULL) end = start + strlen(start);
    while (end > start && isspace((unsigned char)end[-1])) end--;
    while (start < end && isspace((unsigned char)*start)) start++;
    len = (size_t)(end - start);
    if (len + 1 > out_cap) return 0;
    memcpy(out, start, len);
    out[len] = '\0';
    return 1;
}

static int parse_size_field(const char *line, const char *key, size_t *out) {
    char buf[64];

    if (!parse_field(line, key, buf, sizeof(buf))) return 0;
    return parse_size_value(buf, out);
}

static int parse_direct_case_line(const char *line, ManifestCase *out) {
    char work[MAX_LINE];
    char *cursor;
    char *colon;

    if (!copy_text(work, sizeof(work), line)) return 0;
    cursor = trim_ascii(work);
    if (strncmp(cursor, "case ", 5) != 0) return 0;
    cursor += 5;
    colon = strchr(cursor, ':');
    if (colon == NULL) return 0;
    *colon = '\0';
    if (!copy_text(out->case_name, sizeof(out->case_name), trim_ascii(cursor))) {
        return 0;
    }

    return parse_field(line, "input=", out->input, sizeof(out->input)) &&
           parse_field(line,
                       "rule110_initial=",
                       out->initial,
                       sizeof(out->initial)) &&
           parse_size_field(line, "payload_start=", &out->payload_start) &&
           parse_size_field(line, "payload_len=", &out->payload_len);
}

static int parse_token_line(const char *line,
                            const char *key,
                            char *out,
                            size_t out_cap) {
    const char *start = line + strlen(key);

    if (strncmp(line, key, strlen(key)) != 0) return 0;
    while (*start && isspace((unsigned char)*start)) start++;
    return copy_text(out, out_cap, start);
}

static size_t find_payload_start(const char *initial, const char *input) {
    const char *found;
    size_t row_len = strlen(initial);
    size_t input_len = strlen(input);

    if (input_len == 0 || input_len > row_len) return row_len / 2;
    found = strstr(initial, input);
    if (found != NULL) return (size_t)(found - initial);
    return (row_len - input_len) / 2;
}

static size_t choose_evolution_steps(size_t row_len) {
    if (row_len < 100) return 256;
    if (row_len < 300) return 512;
    return 1024;
}

static int module_display_name(const char *dir, char *out, size_t out_cap) {
    if (strcmp(dir, "mark") == 0) return copy_text(out, out_cap, "Mark");
    if (strcmp(dir, "hist") == 0) return copy_text(out, out_cap, "Hist");
    if (strcmp(dir, "ext") == 0) return copy_text(out, out_cap, "Ext");
    if (strcmp(dir, "sig") == 0) return copy_text(out, out_cap, "Sig");
    if (strcmp(dir, "cont") == 0) return copy_text(out, out_cap, "Cont");
    if (strcmp(dir, "bundle") == 0) return copy_text(out, out_cap, "Bundle");
    if (strcmp(dir, "unary") == 0) return copy_text(out, out_cap, "Unary");
    if (strcmp(dir, "ask") == 0) return copy_text(out, out_cap, "Ask");
    if (strcmp(dir, "external_binary") == 0) return copy_text(out, out_cap, "ExternalBinary");
    if (strcmp(dir, "gap") == 0) return copy_text(out, out_cap, "Gap");
    if (strcmp(dir, "package") == 0) return copy_text(out, out_cap, "Package");
    if (strcmp(dir, "name_cert") == 0) return copy_text(out, out_cap, "NameCert");
    if (strcmp(dir, "settled") == 0) return copy_text(out, out_cap, "Settled");
    if (strcmp(dir, "ground_compiler") == 0) return copy_text(out, out_cap, "GroundCompiler");
    if (strcmp(dir, "circle_up") == 0) return copy_text(out, out_cap, "CircleUp");
    if (strcmp(dir, "fold_up") == 0) return copy_text(out, out_cap, "FoldUp");
    if (strcmp(dir, "meta_cic") == 0) return copy_text(out, out_cap, "MetaCIC");
    if (strcmp(dir, "topology_up") == 0) return copy_text(out, out_cap, "TopologyUp");
    return copy_text(out, out_cap, dir);
}

static int manifest_stem(const char *filename, char *out, size_t out_cap) {
    size_t len = strlen(filename);
    const char *suffix = ".r110.ct";
    size_t suffix_len = strlen(suffix);

    if (len <= suffix_len || strcmp(filename + len - suffix_len, suffix) != 0) {
        return 0;
    }
    if (len - suffix_len + 1 > out_cap) return 0;
    memcpy(out, filename, len - suffix_len);
    out[len - suffix_len] = '\0';
    return 1;
}

static void id_slug(const char *src, char *out, size_t out_cap) {
    size_t j = 0;

    for (size_t i = 0; src[i] != '\0' && j + 1 < out_cap; i++) {
        unsigned char c = (unsigned char)src[i];

        if (isalnum(c)) {
            out[j++] = (char)tolower(c);
        } else {
            out[j++] = '_';
        }
    }
    out[j] = '\0';
}

static int operation_id(const Operation *op, char *out, size_t out_cap) {
    char stem[MAX_NAME];
    char case_name[MAX_NAME];

    id_slug(op->manifest_stem, stem, sizeof(stem));
    id_slug(op->manifest_case.case_name, case_name, sizeof(case_name));
    out[0] = '\0';
    return copy_text(out, out_cap, op->module_dir) &&
           append_text(out, out_cap, "__") &&
           append_text(out, out_cap, stem) &&
           append_text(out, out_cap, "__") &&
           append_text(out, out_cap, case_name);
}

static int add_operation(OperationList *ops,
                         const char *module_dir,
                         const char *manifest_file,
                         const char *manifest_stem_text,
                         const ManifestCase *manifest_case) {
    Operation *op;
    Operation *next;
    size_t next_cap;

    if (ops->count == ops->cap) {
        next_cap = ops->cap == 0 ? 64 : ops->cap * 2;
        next = (Operation *)realloc(ops->items, next_cap * sizeof(ops->items[0]));
        if (next == NULL) return 0;
        ops->items = next;
        ops->cap = next_cap;
    }

    op = &ops->items[ops->count];
    memset(op, 0, sizeof(*op));
    if (!copy_text(op->module_dir, sizeof(op->module_dir), module_dir)) return 0;
    if (!module_display_name(module_dir, op->module_name, sizeof(op->module_name))) return 0;
    if (!copy_text(op->manifest_file, sizeof(op->manifest_file), manifest_file)) return 0;
    if (!copy_text(op->manifest_stem, sizeof(op->manifest_stem), manifest_stem_text)) return 0;
    if (!copy_text(op->source_manifest, sizeof(op->source_manifest), "manifests/")) return 0;
    if (!append_text(op->source_manifest, sizeof(op->source_manifest), module_dir)) return 0;
    if (!append_text(op->source_manifest, sizeof(op->source_manifest), "/")) return 0;
    if (!append_text(op->source_manifest, sizeof(op->source_manifest), manifest_file)) return 0;
    op->manifest_case = *manifest_case;
    op->evolution_steps = choose_evolution_steps(strlen(manifest_case->initial));
    ops->count++;
    return 1;
}

static int flush_algo_case(OperationList *ops,
                           const char *module_dir,
                           const char *manifest_file,
                           const char *manifest_stem_text,
                           ManifestCase *cur,
                           int has_case,
                           int has_input,
                           int has_bits) {
    if (!has_case) return 1;
    if (!has_input || !has_bits) return 0;
    cur->payload_len = strlen(cur->input);
    cur->payload_start = find_payload_start(cur->initial, cur->input);
    return add_operation(ops, module_dir, manifest_file, manifest_stem_text, cur);
}

static int load_manifest_file(OperationList *ops,
                              const char *module_dir,
                              const char *manifest_file) {
    char path[MAX_PATH_TEXT];
    char stem[MAX_NAME];
    FILE *f;
    char *line;
    ManifestCase cur;
    int is_algo = 0;
    int has_case = 0;
    int has_input = 0;
    int has_bits = 0;

    path[0] = '\0';
    if (!copy_text(path, sizeof(path), "manifests/")) return 0;
    if (!append_text(path, sizeof(path), module_dir)) return 0;
    if (!append_text(path, sizeof(path), "/")) return 0;
    if (!append_text(path, sizeof(path), manifest_file)) return 0;
    if (!manifest_stem(manifest_file, stem, sizeof(stem))) return 0;

    f = fopen(path, "r");
    if (f == NULL) return 0;
    line = (char *)malloc(MAX_LINE);
    if (line == NULL) {
        fclose(f);
        return 0;
    }
    memset(&cur, 0, sizeof(cur));

    while (fgets(line, MAX_LINE, f) != NULL) {
        char *trimmed = trim_ascii(line);

        if (trimmed[0] == '\0') continue;
        if (strcmp(trimmed, "ALGO_R110_MANIFEST 1") == 0) {
            is_algo = 1;
            continue;
        }
        if (!is_algo && strncmp(trimmed, "case ", 5) == 0) {
            ManifestCase direct_case;

            memset(&direct_case, 0, sizeof(direct_case));
            if (!parse_direct_case_line(trimmed, &direct_case)) {
                fclose(f);
                free(line);
                return 0;
            }
            if (!add_operation(ops, module_dir, manifest_file, stem, &direct_case)) {
                fclose(f);
                free(line);
                return 0;
            }
            continue;
        }
        if (is_algo && strncmp(trimmed, "case ", 5) == 0) {
            if (!flush_algo_case(ops,
                                 module_dir,
                                 manifest_file,
                                 stem,
                                 &cur,
                                 has_case,
                                 has_input,
                                 has_bits)) {
                fclose(f);
                free(line);
                return 0;
            }
            memset(&cur, 0, sizeof(cur));
            if (!copy_text(cur.case_name, sizeof(cur.case_name), trim_ascii(trimmed + 5))) {
                fclose(f);
                free(line);
                return 0;
            }
            has_case = 1;
            has_input = 0;
            has_bits = 0;
            continue;
        }
        if (is_algo && has_case && strncmp(trimmed, "INPUT ", 6) == 0) {
            if (!parse_token_line(trimmed, "INPUT", cur.input, sizeof(cur.input))) {
                fclose(f);
                free(line);
                return 0;
            }
            has_input = 1;
            continue;
        }
        if (is_algo && has_case && strncmp(trimmed, "CENTRAL_BITS ", 13) == 0) {
            if (!parse_token_line(trimmed, "CENTRAL_BITS", cur.initial, sizeof(cur.initial))) {
                fclose(f);
                free(line);
                return 0;
            }
            has_bits = 1;
            continue;
        }
    }

    if (!flush_algo_case(ops,
                         module_dir,
                         manifest_file,
                         stem,
                         &cur,
                         has_case,
                         has_input,
                         has_bits)) {
        fclose(f);
        free(line);
        return 0;
    }
    fclose(f);
    free(line);
    return 1;
}

static int compare_names(const void *a, const void *b) {
    const char *left = (const char *)a;
    const char *right = (const char *)b;

    return strcmp(left, right);
}

static int collect_manifest_names(const char *module_dir, NameList *names) {
    char path[MAX_PATH_TEXT];
    DIR *dir;
    struct dirent *entry;

    memset(names, 0, sizeof(*names));
    path[0] = '\0';
    if (!copy_text(path, sizeof(path), "manifests/")) return 0;
    if (!append_text(path, sizeof(path), module_dir)) return 0;
    dir = opendir(path);
    if (dir == NULL) return 0;

    while ((entry = readdir(dir)) != NULL) {
        if (!ends_with(entry->d_name, ".r110.ct")) continue;
        if (names->count >= sizeof(names->names) / sizeof(names->names[0])) {
            closedir(dir);
            return 0;
        }
        if (!copy_text(names->names[names->count],
                       sizeof(names->names[names->count]),
                       entry->d_name)) {
            closedir(dir);
            return 0;
        }
        names->count++;
    }
    closedir(dir);
    qsort(names->names, names->count, sizeof(names->names[0]), compare_names);
    return 1;
}

static int load_all_operations(OperationList *ops) {
    const size_t module_count = sizeof(MODULE_DIRS) / sizeof(MODULE_DIRS[0]);

    for (size_t i = 0; i < module_count; i++) {
        NameList names;

        if (!collect_manifest_names(MODULE_DIRS[i], &names)) return 0;
        for (size_t j = 0; j < names.count; j++) {
            if (!load_manifest_file(ops, MODULE_DIRS[i], names.names[j])) {
                return 0;
            }
        }
    }
    return 1;
}

static void json_string(FILE *out, const char *s) {
    fputc('"', out);
    for (size_t i = 0; s[i] != '\0'; i++) {
        unsigned char c = (unsigned char)s[i];

        if (c == '"' || c == '\\') {
            fputc('\\', out);
            fputc((int)c, out);
        } else if (c == '\n') {
            fputs("\\n", out);
        } else if (c == '\r') {
            fputs("\\r", out);
        } else if (c == '\t') {
            fputs("\\t", out);
        } else {
            fputc((int)c, out);
        }
    }
    fputc('"', out);
}

static void write_layer(FILE *out,
                        const char *label,
                        size_t x_start,
                        size_t x_end,
                        const char *color,
                        int first) {
    fprintf(out, "%s      {\"label\": ", first ? "" : ",\n");
    json_string(out, label);
    fprintf(out,
            ", \"x_start\": %zu, \"x_end\": %zu, \"color\": ",
            x_start,
            x_end);
    json_string(out, color);
    fputc('}', out);
}

static const CuratedLayers *find_curated_layers(const char *id) {
    const size_t count = sizeof(CURATED) / sizeof(CURATED[0]);

    for (size_t i = 0; i < count; i++) {
        if (strcmp(CURATED[i].id, id) == 0) return &CURATED[i];
    }
    return NULL;
}

static void write_layers(FILE *out, const Operation *op, const char *id) {
    const ManifestCase *manifest_case = &op->manifest_case;
    const size_t row_len = strlen(manifest_case->initial);
    size_t payload_start = manifest_case->payload_start;
    size_t payload_end = payload_start + manifest_case->payload_len;
    const CuratedLayers *curated = find_curated_layers(id);

    if (payload_start > row_len) payload_start = row_len;
    if (payload_end > row_len) payload_end = row_len;

    write_layer(out,
                "left boundary",
                0,
                payload_start,
                "#d9d4c7",
                1);
    write_layer(out,
                "payload",
                payload_start,
                payload_end,
                "#f2c14e",
                0);
    write_layer(out,
                "decode window",
                payload_start,
                payload_end,
                "#e15759",
                0);
    if (curated != NULL) {
        for (size_t i = 0; i < curated->segment_count; i++) {
            const Segment *seg = &curated->segments[i];
            write_layer(out,
                        seg->label,
                        payload_start + seg->offset,
                        payload_start + seg->offset + seg->len,
                        seg->color,
                        0);
        }
    }
    write_layer(out,
                "right boundary",
                payload_end,
                row_len,
                "#d9d4c7",
                0);
}

static void write_operation(FILE *out, const Operation *op, int first) {
    const ManifestCase *manifest_case = &op->manifest_case;
    char id[MAX_PATH_TEXT];
    char display_name[MAX_PATH_TEXT];

    if (!operation_id(op, id, sizeof(id))) exit(1);
    display_name[0] = '\0';
    if (!copy_text(display_name, sizeof(display_name), op->module_name) ||
        !append_text(display_name, sizeof(display_name), " · ") ||
        !append_text(display_name, sizeof(display_name), op->manifest_stem) ||
        !append_text(display_name, sizeof(display_name), " · ") ||
        !append_text(display_name, sizeof(display_name), manifest_case->case_name)) {
        exit(1);
    }

    fprintf(out, "%s  {\n", first ? "" : ",\n");
    fputs("    \"id\": ", out);
    json_string(out, id);
    fputs(",\n    \"module\": ", out);
    json_string(out, op->module_name);
    fputs(",\n    \"manifest_file\": ", out);
    json_string(out, op->manifest_file);
    fputs(",\n    \"case_name\": ", out);
    json_string(out, manifest_case->case_name);
    fputs(",\n    \"name\": ", out);
    json_string(out, display_name);
    fputs(",\n    \"source_manifest\": ", out);
    json_string(out, op->source_manifest);
    fputs(",\n    \"initial_row\": ", out);
    json_string(out, manifest_case->initial);
    fprintf(out, ",\n    \"evolution_steps\": %zu,\n", op->evolution_steps);
    fputs("    \"expected_decode\": {\n", out);
    fputs("      \"relation\": ", out);
    json_string(out, op->manifest_stem);
    fputs(",\n      \"case_input\": ", out);
    json_string(out, manifest_case->input);
    fprintf(out,
            ",\n      \"payload_start\": %zu,\n      \"payload_len\": %zu,\n",
            manifest_case->payload_start,
            manifest_case->payload_len);
    fputs("      \"verdict\": \"pass\"\n", out);
    fputs("    },\n    \"semantic_layers\": [\n", out);
    write_layers(out, op, id);
    fputs("\n    ]\n  }", out);
}

int main(void) {
    OperationList ops;

    memset(&ops, 0, sizeof(ops));
    if (!load_all_operations(&ops)) {
        fprintf(stderr, "reject: failed to read generated Rule 110 manifests\n");
        free(ops.items);
        return 1;
    }
    fputs("{\n", stdout);
    fputs("  \"schema\": \"bedc_rule110_operations_v2\",\n", stdout);
    fputs("  \"generated_by\": \"rule110/tools/bedc_operations_export.c\",\n", stdout);
    fputs("  \"operations\": [\n", stdout);
    for (size_t i = 0; i < ops.count; i++) {
        write_operation(stdout, &ops.items[i], i == 0);
    }
    fputs("\n  ]\n}\n", stdout);
    free(ops.items);
    return 0;
}
