#include "cook_decode.h"
#include "cook_encode.h"
#include "manifest_runner.h"
#include "rule110.h"

#include <assert.h>
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define TARGET_MANIFEST "manifests/hist/hsame_refl.algo.ct"
#define TARGET_CASE "empty"
#define DECODE_STEPS 512
#define MAX_BITS 4096

typedef struct {
    char input[MAX_BITS];
    char expected[MAX_BITS];
} ManifestCase;

static char *trim_ascii(char *s) {
    char *end;

    while (*s && isspace((unsigned char)*s)) s++;
    end = s + strlen(s);
    while (end > s && isspace((unsigned char)end[-1])) end--;
    *end = '\0';
    return s;
}

static int copy_value(char *dst, size_t dst_cap, const char *src) {
    size_t len = strlen(src);

    if (len + 1 > dst_cap) return 0;
    memcpy(dst, src, len + 1);
    return 1;
}

static int is_bit_string(const char *s) {
    if (s == NULL || s[0] == '\0') return 0;
    for (size_t i = 0; s[i] != '\0'; i++) {
        if (s[i] != '0' && s[i] != '1') return 0;
    }
    return 1;
}

static int parse_case_line(char *line,
                           const char *case_name,
                           ManifestCase *out) {
    char *cursor;
    char *colon;
    char *field;

    if (strncmp(line, "case ", 5) != 0) return 0;
    cursor = line + 5;
    colon = strchr(cursor, ':');
    if (colon == NULL) return 0;
    *colon = '\0';
    if (strcmp(trim_ascii(cursor), case_name) != 0) return 0;

    out->input[0] = '\0';
    out->expected[0] = '\0';
    field = strtok(colon + 1, ";");
    while (field != NULL) {
        char *eq;
        char *key;
        char *value;

        field = trim_ascii(field);
        eq = strchr(field, '=');
        if (eq == NULL) return 0;
        *eq = '\0';
        key = trim_ascii(field);
        value = trim_ascii(eq + 1);
        if (strcmp(key, "input") == 0) {
            if (!copy_value(out->input, sizeof(out->input), value)) return 0;
        } else if (strcmp(key, "expected_certificate") == 0) {
            if (!copy_value(out->expected, sizeof(out->expected), value)) {
                return 0;
            }
        }
        field = strtok(NULL, ";");
    }

    return is_bit_string(out->input) && is_bit_string(out->expected);
}

static int load_manifest_case(const char *path,
                              const char *case_name,
                              ManifestCase *out) {
    FILE *f = fopen(path, "r");
    char line[8192];

    if (f == NULL) return 0;
    while (fgets(line, sizeof(line), f) != NULL) {
        size_t len = strlen(line);
        char *trimmed;

        if (len > 0 && line[len - 1] == '\n') line[--len] = '\0';
        if (len > 0 && line[len - 1] == '\r') line[--len] = '\0';
        trimmed = trim_ascii(line);
        if (trimmed[0] == '\0' || trimmed[0] == '#') continue;
        if (trimmed != line) memmove(line, trimmed, strlen(trimmed) + 1);
        if (parse_case_line(line, case_name, out)) {
            fclose(f);
            return 1;
        }
    }
    fclose(f);
    return 0;
}

static uint8_t *bit_string_to_bytes(const char *bits, size_t *out_len) {
    size_t len = strlen(bits);
    uint8_t *out = (uint8_t *)malloc(len ? len : 1);

    assert(out != NULL);
    for (size_t i = 0; i < len; i++) {
        assert(bits[i] == '0' || bits[i] == '1');
        out[i] = (uint8_t)(bits[i] == '1');
    }
    *out_len = len;
    return out;
}

static void bit_string_to_decoded_symbols(const char *bits,
                                          char *out,
                                          size_t out_cap) {
    size_t len = strlen(bits);

    assert(len + 1 <= out_cap);
    for (size_t i = 0; i < len; i++) {
        assert(bits[i] == '0' || bits[i] == '1');
        out[i] = bits[i] == '1' ? 'Y' : 'N';
    }
    out[len] = '\0';
}

static void test_hist_hsame_refl_full_roundtrip(void) {
    MrCtProgram program;
    ManifestCase manifest_case;
    uint8_t *tape;
    uint8_t placeholder = 0;
    uint8_t *cells = NULL;
    char decoded[MAX_BITS];
    char expected_decoded[MAX_BITS];
    size_t tape_len = 0;
    size_t written = 0;
    int rc;
    CyclicTagInput ct;

    assert(mr_load_ct_program(TARGET_MANIFEST, &program) == 0);
    assert(program.num_prods == 16);
    assert(load_manifest_case(TARGET_MANIFEST,
                              TARGET_CASE,
                              &manifest_case));
    assert(strcmp(manifest_case.input, "1111") == 0);
    assert(strcmp(manifest_case.expected, "10000100011001010011") == 0);

    tape = bit_string_to_bytes(manifest_case.input, &tape_len);
    bit_string_to_decoded_symbols(manifest_case.expected,
                                  expected_decoded,
                                  sizeof(expected_decoded));
    ct.productions = program.prods;
    ct.prod_lens = program.prod_lens;
    ct.num_productions = program.num_prods;
    ct.initial_tape = tape;
    ct.tape_len = tape_len;

    rc = cook_encode_phase_exact(&ct, &placeholder, 0, &written);
    assert(rc == COOK_ENCODE_PHASE_EXACT_INSUFFICIENT_BUFFER);
    assert(written > 0);

    cells = (uint8_t *)malloc(written);
    assert(cells != NULL);
    rc = cook_encode_phase_exact(&ct, cells, written, &written);
    assert(rc == COOK_ENCODE_PHASE_EXACT_OK);

    r110_run_n_steps(cells, written, DECODE_STEPS);
    rc = cook_decode_output(cells, written, decoded, sizeof(decoded));
    assert(rc == COOK_DECODE_OK);
    if (strcmp(decoded, expected_decoded) != 0) {
        fprintf(stderr,
                "decoded mismatch: got=%s expected=%s steps=%d\n",
                decoded,
                expected_decoded,
                DECODE_STEPS);
    }
    assert(strcmp(decoded, expected_decoded) == 0);

    free(cells);
    free(tape);
    mr_free_ct_program(&program);
    printf("  hist_hsame_refl.algo full roundtrip: PASS\n");
}

int main(void) {
    printf("== test_enum_cook_full_roundtrip ==\n");
    test_hist_hsame_refl_full_roundtrip();
    printf("ALL test_enum_cook_full_roundtrip tests passed\n");
    return 0;
}
