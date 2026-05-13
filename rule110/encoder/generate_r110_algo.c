#include "cook_encode.h"
#include "cyclic_tag.h"
#include "rule110.h"

#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define MAX_NAME 128
#define MAX_BITS 8192
#define MAX_LINE 16384

typedef struct {
    char name[MAX_NAME];
    char input[MAX_BITS];
    char expected_ct[MAX_BITS];
    int has_input;
    int has_expected_ct;
} AlgoCase;

typedef struct {
    uint8_t **productions;
    size_t *prod_lens;
    size_t num_productions;
    AlgoCase *cases;
    size_t case_count;
    size_t assertion_count;
} AlgoManifest;

static void manifest_init(AlgoManifest *m) {
    m->productions = NULL;
    m->prod_lens = NULL;
    m->num_productions = 0;
    m->cases = NULL;
    m->case_count = 0;
    m->assertion_count = 0;
}

static void manifest_free(AlgoManifest *m) {
    for (size_t i = 0; i < m->num_productions; i++) free(m->productions[i]);
    free(m->productions);
    free(m->prod_lens);
    free(m->cases);
    manifest_init(m);
}

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

static int copy_text(char *dst, size_t dst_cap, const char *src) {
    size_t len = strlen(src);

    if (len + 1 > dst_cap) return 0;
    memcpy(dst, src, len + 1);
    return 1;
}

static int parse_bits_alloc(const char *s, uint8_t **out, size_t *out_len) {
    size_t len = strlen(s);
    uint8_t *bits = NULL;

    bits = (uint8_t *)malloc(len ? len : 1);
    if (bits == NULL) return 0;
    for (size_t i = 0; i < len; i++) {
        if (s[i] != '0' && s[i] != '1') {
            free(bits);
            return 0;
        }
        bits[i] = (uint8_t)(s[i] == '1');
    }

    *out = bits;
    *out_len = len;
    return 1;
}

static void write_bits(FILE *f, const uint8_t *bits, size_t len) {
    for (size_t i = 0; i < len; i++) fputc(bits[i] ? '1' : '0', f);
    fputc('\n', f);
}

static int parse_case_line(char *line, AlgoCase *out) {
    char *cursor = trim_ascii(line);
    char *colon = NULL;
    char *field = NULL;

    memset(out, 0, sizeof(*out));
    if (strncmp(cursor, "case ", 5) != 0) return 0;
    cursor += 5;
    colon = strchr(cursor, ':');
    if (colon == NULL) return 0;
    *colon = '\0';
    if (!copy_text(out->name, sizeof(out->name), trim_ascii(cursor))) return 0;

    field = colon + 1;
    for (;;) {
        char *semi = strchr(field, ';');
        char *eq = NULL;
        char *key = NULL;
        char *value = NULL;

        if (semi != NULL) *semi = '\0';
        field = trim_ascii(field);
        if (*field != '\0') {
            eq = strchr(field, '=');
            if (eq == NULL) return 0;
            *eq = '\0';
            key = trim_ascii(field);
            value = trim_ascii(eq + 1);
            if (strcmp(key, "input") == 0) {
                if (!copy_text(out->input, sizeof(out->input), value)) return 0;
                out->has_input = 1;
            } else if (strcmp(key, "expected_certificate") == 0) {
                if (!copy_text(out->expected_ct,
                               sizeof(out->expected_ct),
                               value)) {
                    return 0;
                }
                out->has_expected_ct = 1;
            }
        }

        if (semi == NULL) break;
        field = semi + 1;
    }

    return out->has_input;
}

static int load_manifest(const char *path, AlgoManifest *out) {
    FILE *f = fopen(path, "r");
    char line_buf[MAX_LINE];
    size_t production_index = 0;
    int reading_productions = 0;
    int saw_assertions = 0;

    if (f == NULL) return 0;
    manifest_init(out);

    while (fgets(line_buf, sizeof(line_buf), f) != NULL) {
        char *line = trim_ascii(line_buf);

        if (reading_productions && production_index < out->num_productions) {
            if (!parse_bits_alloc(line,
                                  &out->productions[production_index],
                                  &out->prod_lens[production_index])) {
                fclose(f);
                manifest_free(out);
                return 0;
            }
            production_index++;
            if (production_index == out->num_productions) {
                reading_productions = 0;
            }
            continue;
        }

        if (line[0] == '\0' || line[0] == '#') continue;
        if (strncmp(line, "PRODUCTIONS ", 12) == 0) {
            if (!parse_size_value(line + 12, &out->num_productions)) {
                fclose(f);
                manifest_free(out);
                return 0;
            }
            out->productions =
                (uint8_t **)calloc(out->num_productions ? out->num_productions : 1,
                                   sizeof(uint8_t *));
            out->prod_lens =
                (size_t *)calloc(out->num_productions ? out->num_productions : 1,
                                 sizeof(size_t));
            if (out->productions == NULL || out->prod_lens == NULL) {
                fclose(f);
                manifest_free(out);
                return 0;
            }
            reading_productions = 1;
            production_index = 0;
        } else if (strncmp(line, "ASSERTIONS ", 11) == 0) {
            if (!parse_size_value(line + 11, &out->assertion_count)) {
                fclose(f);
                manifest_free(out);
                return 0;
            }
            out->cases = (AlgoCase *)calloc(out->assertion_count ?
                                            out->assertion_count : 1,
                                            sizeof(AlgoCase));
            if (out->cases == NULL) {
                fclose(f);
                manifest_free(out);
                return 0;
            }
            saw_assertions = 1;
        } else if (strncmp(line, "case ", 5) == 0) {
            if (!saw_assertions || out->case_count >= out->assertion_count) {
                fclose(f);
                manifest_free(out);
                return 0;
            }
            if (!parse_case_line(line, &out->cases[out->case_count])) {
                fclose(f);
                manifest_free(out);
                return 0;
            }
            out->case_count++;
        }
    }

    fclose(f);
    return out->productions != NULL &&
           production_index == out->num_productions &&
           saw_assertions &&
           out->case_count == out->assertion_count;
}

static int run_ct_reference(const AlgoManifest *m,
                            const AlgoCase *c,
                            uint8_t **final_out,
                            size_t *final_len_out,
                            size_t *steps_out) {
    uint8_t *input = NULL;
    size_t input_len = 0;
    CtState state;
    CtHaltReason halt;

    if (!parse_bits_alloc(c->input, &input, &input_len)) return 0;
    if (ct_init(&state,
                m->productions,
                m->prod_lens,
                m->num_productions,
                input,
                input_len,
                8192) != 0) {
        free(input);
        return 0;
    }
    halt = ct_run_until_halt(&state, input_len);
    if (halt != CT_HALT_EMPTY && halt != CT_HALT_STEPLIMIT) {
        ct_free(&state);
        free(input);
        return 0;
    }

    *final_out = (uint8_t *)malloc(state.tape_len ? state.tape_len : 1);
    if (*final_out == NULL) {
        ct_free(&state);
        free(input);
        return 0;
    }
    memcpy(*final_out, state.tape, state.tape_len);
    *final_len_out = state.tape_len;
    *steps_out = state.steps_taken;

    ct_free(&state);
    free(input);
    return 1;
}

static int expected_matches(const AlgoCase *c,
                            const uint8_t *final_bits,
                            size_t final_len) {
    if (!c->has_expected_ct) return 1;
    if (strlen(c->expected_ct) != final_len) return 0;
    for (size_t i = 0; i < final_len; i++) {
        if ((c->expected_ct[i] == '1') != (final_bits[i] == 1)) return 0;
    }
    return 1;
}

static int make_output_path(const char *input_path,
                            char *out_path,
                            size_t out_path_cap) {
    const char *suffix = ".algo.ct";
    size_t path_len = strlen(input_path);
    size_t suffix_len = strlen(suffix);

    if (path_len <= suffix_len ||
        strcmp(input_path + path_len - suffix_len, suffix) != 0) {
        return 0;
    }
    if (path_len - suffix_len + strlen(".algo.r110.ct") + 1 > out_path_cap) {
        return 0;
    }
    memcpy(out_path, input_path, path_len - suffix_len);
    out_path[path_len - suffix_len] = '\0';
    strcat(out_path, ".algo.r110.ct");
    return 1;
}

static int write_algo_r110_manifest(const char *source_path,
                                    const char *out_path,
                                    const AlgoManifest *m,
                                    size_t rule110_steps) {
    FILE *out = fopen(out_path, "w");
    uint8_t placeholder = 0;

    if (out == NULL) return 0;

    fprintf(out, "ALGO_R110_MANIFEST 1\n");
    fprintf(out, "SOURCE_CT %s\n", source_path);
    fprintf(out, "CONSTRUCTION cook_phase_exact_packet_diagnostic\n");
    fprintf(out, "EVOLUTION_STEPS %zu\n", rule110_steps);
    fprintf(out, "ASSERTIONS %zu\n", m->case_count);

    for (size_t i = 0; i < m->case_count; i++) {
        const AlgoCase *c = &m->cases[i];
        uint8_t *input = NULL;
        size_t input_len = 0;
        uint8_t *ct_final = NULL;
        size_t ct_final_len = 0;
        size_t ct_steps = 0;
        CyclicTagInput encode_input;
        uint8_t *initial = NULL;
        uint8_t *final = NULL;
        size_t required = 0;
        int rc;

        if (!parse_bits_alloc(c->input, &input, &input_len) ||
            !run_ct_reference(m, c, &ct_final, &ct_final_len, &ct_steps) ||
            !expected_matches(c, ct_final, ct_final_len)) {
            free(input);
            free(ct_final);
            fclose(out);
            return 0;
        }

        encode_input.productions = m->productions;
        encode_input.prod_lens = m->prod_lens;
        encode_input.num_productions = m->num_productions;
        encode_input.initial_tape = input;
        encode_input.tape_len = input_len;

        rc = cook_encode_phase_exact(&encode_input,
                                     &placeholder,
                                     0,
                                     &required);
        if (rc != COOK_ENCODE_PHASE_EXACT_INSUFFICIENT_BUFFER ||
            required == 0) {
            free(input);
            free(ct_final);
            fclose(out);
            return 0;
        }

        initial = (uint8_t *)malloc(required);
        final = (uint8_t *)malloc(required);
        if (initial == NULL || final == NULL) {
            free(initial);
            free(final);
            free(input);
            free(ct_final);
            fclose(out);
            return 0;
        }

        rc = cook_encode_phase_exact(&encode_input,
                                     initial,
                                     required,
                                     &required);
        if (rc != COOK_ENCODE_PHASE_EXACT_OK) {
            free(initial);
            free(final);
            free(input);
            free(ct_final);
            fclose(out);
            return 0;
        }
        memcpy(final, initial, required);
        r110_run_n_steps(final, required, rule110_steps);

        fprintf(out, "case %s\n", c->name);
        fprintf(out, "INPUT %s\n", c->input);
        fprintf(out, "CT_STEPS %zu\n", ct_steps);
        fprintf(out, "CT_FINAL %zu\n", ct_final_len);
        write_bits(out, ct_final, ct_final_len);
        fprintf(out, "RULE110_INITIAL %zu\n", required);
        write_bits(out, initial, required);
        fprintf(out, "RULE110_FINAL %zu\n", required);
        write_bits(out, final, required);
        fprintf(out, "ENDCASE\n");

        free(initial);
        free(final);
        free(input);
        free(ct_final);
    }

    fclose(out);
    return 1;
}

int main(int argc, char **argv) {
    AlgoManifest manifest;
    char out_path[1024];
    size_t rule110_steps = 128;

    if (argc != 2 && argc != 3 && argc != 4) {
        fprintf(stderr,
                "usage: %s <input.algo.ct> [output.algo.r110.ct] [steps]\n",
                argv[0]);
        return 2;
    }
    if (!load_manifest(argv[1], &manifest)) {
        fprintf(stderr, "reject: failed to parse source manifest %s\n", argv[1]);
        return 1;
    }
    if (manifest.num_productions == 0) {
        fprintf(stderr, "reject: .algo Cook path requires PRODUCTIONS > 0\n");
        manifest_free(&manifest);
        return 1;
    }

    if (argc >= 3) {
        if (!copy_text(out_path, sizeof(out_path), argv[2])) {
            fprintf(stderr, "reject: output path too long\n");
            manifest_free(&manifest);
            return 2;
        }
    } else if (!make_output_path(argv[1], out_path, sizeof(out_path))) {
        fprintf(stderr, "reject: input path must end in .algo.ct\n");
        manifest_free(&manifest);
        return 2;
    }
    if (argc == 4 && !parse_size_value(argv[3], &rule110_steps)) {
        fprintf(stderr, "reject: invalid steps\n");
        manifest_free(&manifest);
        return 2;
    }

    if (!write_algo_r110_manifest(argv[1],
                                  out_path,
                                  &manifest,
                                  rule110_steps)) {
        fprintf(stderr, "reject: failed to write %s\n", out_path);
        manifest_free(&manifest);
        return 1;
    }

    printf("%s: generated %zu Cook diagnostic case(s), steps=%zu\n",
           out_path,
           manifest.case_count,
           rule110_steps);
    manifest_free(&manifest);
    return 0;
}
