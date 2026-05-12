#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

#define MAX_CASES 512
#define MAX_NAME 128
#define MAX_BITS 2048
#define MAX_LINE 4096
#define PAYLOAD_PAD_LEFT 16
#define PAYLOAD_PAD_RIGHT 16
#define MIN_INITIAL_LENGTH 48

typedef struct {
    char name[MAX_NAME];
    char input[MAX_BITS];
    int has_input;
    int skipped;
    char skip_reason[64];
} SourceCase;

typedef struct {
    SourceCase cases[MAX_CASES];
    size_t case_count;
    size_t assertion_count;
    size_t productions;
    int saw_productions;
    int saw_assertions;
} SourceManifest;

static char *trim_ascii(char *s) {
    char *end;

    while (*s && isspace((unsigned char)*s)) s++;
    end = s + strlen(s);
    while (end > s && isspace((unsigned char)end[-1])) end--;
    *end = '\0';
    return s;
}

static int parse_size_arg(const char *s, size_t *out) {
    char *end = NULL;
    unsigned long value;

    if (s == NULL || s[0] == '\0') return 0;
    value = strtoul(s, &end, 10);
    if (end == s) return 0;
    while (*end && isspace((unsigned char)*end)) end++;
    if (*end != '\0') return 0;
    *out = (size_t)value;
    return 1;
}

static int copy_text(char *dst, size_t dst_cap, const char *src) {
    size_t len = strlen(src);

    if (len + 1 > dst_cap) return 0;
    memcpy(dst, src, len + 1);
    return 1;
}

static int is_binary_string_or_empty(const char *s) {
    if (s == NULL) return 0;
    for (size_t i = 0; s[i] != '\0'; i++) {
        if (s[i] != '0' && s[i] != '1') return 0;
    }
    return 1;
}

static int normalize_input(char *dst, size_t dst_cap, const char *value) {
    if (strcmp(value, "<empty>") == 0) {
        return copy_text(dst, dst_cap, "");
    }
    return copy_text(dst, dst_cap, value);
}

static int parse_case_line(char *line, SourceCase *out) {
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
    if (!copy_text(out->name, sizeof(out->name), trim_ascii(cursor))) {
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

    if (!out->has_input) {
        out->skipped = 1;
        return copy_text(out->skip_reason,
                         sizeof(out->skip_reason),
                         "no_input_field")
                   ? 1
                   : -1;
    }
    if (!is_binary_string_or_empty(out->input)) {
        out->skipped = 1;
        return copy_text(out->skip_reason,
                         sizeof(out->skip_reason),
                         "nonbinary_input")
                   ? 1
                   : -1;
    }

    return 1;
}

static int parse_source_manifest(const char *path, SourceManifest *out) {
    FILE *f = fopen(path, "r");
    char line_buf[MAX_LINE];

    if (f == NULL) return 0;
    memset(out, 0, sizeof(*out));

    while (fgets(line_buf, sizeof(line_buf), f) != NULL) {
        char *line = trim_ascii(line_buf);

        if (line[0] == '\0' || line[0] == '#') continue;
        if (strncmp(line, "PRODUCTIONS ", 12) == 0) {
            if (!parse_size_arg(line + 12, &out->productions)) {
                fclose(f);
                return 0;
            }
            out->saw_productions = 1;
        } else if (strncmp(line, "ASSERTIONS ", 11) == 0) {
            if (!parse_size_arg(line + 11, &out->assertion_count)) {
                fclose(f);
                return 0;
            }
            out->saw_assertions = 1;
        } else if (strncmp(line, "case ", 5) == 0) {
            int rc;

            if (out->case_count >= MAX_CASES) {
                fclose(f);
                return 0;
            }
            rc = parse_case_line(line, &out->cases[out->case_count]);
            if (rc <= 0) {
                fclose(f);
                return 0;
            }
            out->case_count++;
        }
    }

    fclose(f);
    return out->saw_productions && out->saw_assertions &&
           out->assertion_count == out->case_count;
}

static void print_bits(FILE *out, const uint8_t *bits, size_t len) {
    for (size_t i = 0; i < len; i++) fputc(bits[i] ? '1' : '0', out);
}

static int make_output_path(const char *input_path,
                            char *out_path,
                            size_t out_path_cap) {
    const char *suffix = ".enum.ct";
    size_t path_len = strlen(input_path);
    size_t suffix_len = strlen(suffix);

    if (path_len <= suffix_len ||
        strcmp(input_path + path_len - suffix_len, suffix) != 0) {
        return 0;
    }
    if (path_len - suffix_len + strlen(".r110.ct") + 1 > out_path_cap) {
        return 0;
    }

    memcpy(out_path, input_path, path_len - suffix_len);
    out_path[path_len - suffix_len] = '\0';
    strcat(out_path, ".r110.ct");
    return 1;
}

static size_t generated_case_count(const SourceManifest *manifest) {
    size_t count = 0;

    for (size_t i = 0; i < manifest->case_count; i++) {
        if (!manifest->cases[i].skipped) count++;
    }
    return count;
}

static int write_r110_manifest(const char *source_path,
                               const char *out_path,
                               const SourceManifest *manifest) {
    FILE *out = fopen(out_path, "w");
    size_t max_payload_len = 0;
    size_t initial_len;
    size_t generated = generated_case_count(manifest);

    if (out == NULL) return 0;

    for (size_t i = 0; i < manifest->case_count; i++) {
        size_t len;

        if (manifest->cases[i].skipped) continue;
        len = strlen(manifest->cases[i].input);
        if (len > max_payload_len) max_payload_len = len;
    }

    initial_len = PAYLOAD_PAD_LEFT + max_payload_len + PAYLOAD_PAD_RIGHT;
    if (initial_len < MIN_INITIAL_LENGTH) initial_len = MIN_INITIAL_LENGTH;

    fprintf(out, "R110_MANIFEST 1\n");
    fprintf(out, "SOURCE_CT %s\n", source_path);
    fprintf(out, "CONSTRUCTION direct_initial_payload\n");
    fprintf(out, "INITIAL_LENGTH %zu\n", initial_len);
    fprintf(out, "ASSERTIONS %zu\n", generated);

    for (size_t i = 0; i < manifest->case_count; i++) {
        const SourceCase *c = &manifest->cases[i];
        size_t payload_len;
        uint8_t *initial;

        if (c->skipped) {
            fprintf(out, "skip %s: reason=%s\n", c->name, c->skip_reason);
            continue;
        }

        payload_len = strlen(c->input);
        initial = (uint8_t *)calloc(initial_len ? initial_len : 1,
                                    sizeof(uint8_t));
        if (initial == NULL) {
            free(initial);
            fclose(out);
            return 0;
        }

        for (size_t j = 0; j < payload_len; j++) {
            initial[PAYLOAD_PAD_LEFT + j] = (uint8_t)(c->input[j] == '1');
        }

        fprintf(out, "case %s: input=%s ; rule110_initial=",
                c->name,
                c->input);
        print_bits(out, initial, initial_len);
        fprintf(out,
                " ; steps=0 ; payload_start=%d ; payload_len=%zu ; expected_payload=%s ; encoding=direct_bit_payload ; construction=direct_initial_payload\n",
                PAYLOAD_PAD_LEFT,
                payload_len,
                c->input);

        free(initial);
    }

    fclose(out);
    return 1;
}

int main(int argc, char **argv) {
    SourceManifest manifest;
    char out_path[1024];

    if (argc != 2 && argc != 3) {
        fprintf(stderr, "usage: %s <input.enum.ct> [output.r110.ct]\n", argv[0]);
        return 2;
    }

    if (!parse_source_manifest(argv[1], &manifest)) {
        fprintf(stderr, "reject: failed to parse source manifest %s\n", argv[1]);
        return 1;
    }
    if (manifest.productions != 0) {
        fprintf(stderr,
                "skip: direct carrier requires PRODUCTIONS 0, got %zu\n",
                manifest.productions);
        return 3;
    }

    if (argc == 3) {
        if (!copy_text(out_path, sizeof(out_path), argv[2])) {
            fprintf(stderr, "reject: output path too long\n");
            return 2;
        }
    } else if (!make_output_path(argv[1], out_path, sizeof(out_path))) {
        fprintf(stderr, "reject: input path must end in .enum.ct\n");
        return 2;
    }

    if (!write_r110_manifest(argv[1], out_path, &manifest)) {
        fprintf(stderr, "reject: failed to write %s\n", out_path);
        return 1;
    }

    printf("%s: generated %zu direct-carrier case(s)",
           out_path,
           generated_case_count(&manifest));
    if (generated_case_count(&manifest) != manifest.case_count) {
        printf(" from %zu source assertion(s)", manifest.case_count);
    }
    printf("\n");
    return 0;
}
