#include <ctype.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_LINE 4096
#define MAX_NAME 128
#define MAX_BITS 2048

typedef struct {
    const char *label;
    size_t offset;
    size_t len;
    const char *color;
} Segment;

typedef struct {
    const char *id;
    const char *display_name;
    const char *manifest_path;
    size_t case_index;
    const char *relation;
    const char *verdict;
    const Segment *segments;
    size_t segment_count;
    size_t evolution_steps;
} OperationSpec;

typedef struct {
    char case_name[MAX_NAME];
    char input[MAX_BITS];
    char initial[MAX_BITS];
    size_t payload_start;
    size_t payload_len;
} ManifestCase;

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

static const OperationSpec OPERATIONS[] = {
    {
        "msame_refl_b0_b0",
        "msame_refl on b0 and b0",
        "manifests/mark/msame_refl.r110.ct",
        0,
        "msame b0 b0",
        "pass",
        MSAME_SEGMENTS,
        sizeof(MSAME_SEGMENTS) / sizeof(MSAME_SEGMENTS[0]),
        256
    },
    {
        "hsame_refl_empty",
        "hsame_refl on Empty",
        "manifests/hist/hsame_refl.r110.ct",
        0,
        "hsame Empty Empty",
        "pass",
        HSAME_SEGMENTS,
        sizeof(HSAME_SEGMENTS) / sizeof(HSAME_SEGMENTS[0]),
        256
    },
    {
        "ext_step_empty_b0",
        "ext_step from Empty by b0",
        "manifests/ext/ext_step.r110.ct",
        0,
        "Ext Empty b0 (e0 Empty)",
        "pass",
        EXT_SEGMENTS,
        sizeof(EXT_SEGMENTS) / sizeof(EXT_SEGMENTS[0]),
        256
    },
    {
        "cont_empty_empty",
        "cont_basic on Empty, Empty",
        "manifests/cont/cont_basic.r110.ct",
        0,
        "Cont Empty Empty Empty",
        "pass",
        CONT_SEGMENTS,
        sizeof(CONT_SEGMENTS) / sizeof(CONT_SEGMENTS[0]),
        256
    }
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
    while (*start && isspace((unsigned char)*start)) start++;
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

static int parse_case_line(const char *line, ManifestCase *out) {
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

static int load_manifest_case(const char *path,
                              size_t case_index,
                              ManifestCase *out) {
    FILE *f = fopen(path, "r");
    char line[MAX_LINE];
    size_t seen = 0;

    if (f == NULL) return 0;
    memset(out, 0, sizeof(*out));
    while (fgets(line, sizeof(line), f) != NULL) {
        char *trimmed = trim_ascii(line);

        if (strncmp(trimmed, "case ", 5) != 0) continue;
        if (seen == case_index) {
            int ok = parse_case_line(trimmed, out);
            fclose(f);
            return ok;
        }
        seen++;
    }
    fclose(f);
    return 0;
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

static void write_operation(FILE *out,
                            const OperationSpec *spec,
                            const ManifestCase *manifest_case,
                            int first) {
    size_t payload_end = manifest_case->payload_start + manifest_case->payload_len;

    fprintf(out, "%s  {\n", first ? "" : ",\n");
    fputs("    \"id\": ", out);
    json_string(out, spec->id);
    fputs(",\n    \"name\": ", out);
    json_string(out, spec->display_name);
    fputs(",\n    \"source_manifest\": ", out);
    json_string(out, spec->manifest_path);
    fputs(",\n    \"case_name\": ", out);
    json_string(out, manifest_case->case_name);
    fputs(",\n    \"initial_row\": ", out);
    json_string(out, manifest_case->initial);
    fprintf(out, ",\n    \"evolution_steps\": %zu,\n", spec->evolution_steps);
    fputs("    \"expected_decode\": {\n", out);
    fputs("      \"relation\": ", out);
    json_string(out, spec->relation);
    fputs(",\n      \"case_input\": ", out);
    json_string(out, manifest_case->input);
    fputs(",\n      \"payload_start\": ", out);
    fprintf(out, "%zu,\n      \"payload_len\": %zu,\n", manifest_case->payload_start, manifest_case->payload_len);
    fputs("      \"verdict\": ", out);
    json_string(out, spec->verdict);
    fputs("\n    },\n    \"semantic_layers\": [\n", out);

    write_layer(out,
                "left fixed-zero boundary",
                0,
                manifest_case->payload_start,
                "#d9d4c7",
                1);
    write_layer(out,
                "BEDC encoded input payload",
                manifest_case->payload_start,
                payload_end,
                "#f2c14e",
                0);
    write_layer(out,
                "decode window",
                manifest_case->payload_start,
                payload_end,
                "#e15759",
                0);
    for (size_t i = 0; i < spec->segment_count; i++) {
        const Segment *seg = &spec->segments[i];
        write_layer(out,
                    seg->label,
                    manifest_case->payload_start + seg->offset,
                    manifest_case->payload_start + seg->offset + seg->len,
                    seg->color,
                    0);
    }
    write_layer(out,
                "right fixed-zero boundary",
                payload_end,
                strlen(manifest_case->initial),
                "#d9d4c7",
                0);
    fputs("\n    ]\n  }", out);
}

int main(void) {
    const size_t op_count = sizeof(OPERATIONS) / sizeof(OPERATIONS[0]);
    ManifestCase cases[sizeof(OPERATIONS) / sizeof(OPERATIONS[0])];

    for (size_t i = 0; i < op_count; i++) {
        if (!load_manifest_case(OPERATIONS[i].manifest_path,
                                OPERATIONS[i].case_index,
                                &cases[i])) {
            fprintf(stderr,
                    "reject: failed to read case %zu from %s\n",
                    OPERATIONS[i].case_index,
                    OPERATIONS[i].manifest_path);
            return 1;
        }
    }

    fputs("{\n", stdout);
    fputs("  \"schema\": \"bedc_rule110_operations\",\n", stdout);
    fputs("  \"generated_by\": \"rule110/tools/bedc_operations_export.c\",\n", stdout);
    fputs("  \"operations\": [\n", stdout);
    for (size_t i = 0; i < op_count; i++) {
        write_operation(stdout, &OPERATIONS[i], &cases[i], i == 0);
    }
    fputs("\n  ]\n}\n", stdout);
    return 0;
}
