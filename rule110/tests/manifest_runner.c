#include "manifest_runner.h"
#include "cyclic_tag.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <ctype.h>

/* Parse manifest file. Format (very simple line-based):
 *   # comment lines start with '#'
 *   PRODUCTIONS <N>
 *   <bit-string> for each production (N lines, blank line = empty production)
 *   ASSERTIONS <K>   (ignored at parse time; runner takes inputs directly)
 *
 * For Tasks 6-9, the runner is invoked by test_mark.c which already knows
 * the input bits and expected outputs (encoded in the test source as
 * assertions). The .ct manifest file contributes the PRODUCTIONS section
 * which defines the CT program. */

static char *bit_string_to_bytes(const char *s, size_t *out_len) {
    size_t n = strlen(s);
    char *b = (char *)malloc(n ? n : 1);
    size_t j = 0;
    for (size_t i = 0; i < n; i++) {
        if (s[i] == '0' || s[i] == '1') b[j++] = s[i] - '0';
    }
    *out_len = j;
    return b;
}

typedef struct {
    uint8_t **prods;
    size_t   *prod_lens;
    size_t    num_prods;
} ParsedManifest;

static int parse_manifest(const char *path, ParsedManifest *out) {
    FILE *f = fopen(path, "r");
    if (!f) return -1;
    char line[1024];
    out->num_prods = 0;
    out->prods = NULL;
    out->prod_lens = NULL;

    while (fgets(line, sizeof(line), f)) {
        if (line[0] == '#' || line[0] == '\n') continue;
        if (strncmp(line, "PRODUCTIONS", 11) == 0) {
            size_t n = (size_t)strtoul(line + 11, NULL, 10);
            out->num_prods = n;
            out->prods = (uint8_t **)calloc(n + 1, sizeof(uint8_t *));
            out->prod_lens = (size_t *)calloc(n + 1, sizeof(size_t));
            for (size_t i = 0; i < n; i++) {
                if (!fgets(line, sizeof(line), f)) { fclose(f); return -1; }
                /* trim newline */
                size_t L = strlen(line);
                if (L > 0 && line[L-1] == '\n') line[--L] = 0;
                size_t bl;
                char *bits = bit_string_to_bytes(line, &bl);
                out->prods[i] = (uint8_t *)bits;
                out->prod_lens[i] = bl;
            }
            break;
        }
    }
    fclose(f);
    /* Need at least one production for ct_run_until_halt to avoid divide-by-zero. */
    if (out->num_prods == 0) {
        /* Free the empty arrays allocated above when PRODUCTIONS was parsed as 0. */
        free(out->prods);
        free(out->prod_lens);
        out->num_prods = 1;
        out->prods = (uint8_t **)calloc(2, sizeof(uint8_t *));
        out->prod_lens = (size_t *)calloc(2, sizeof(size_t));
        out->prods[0] = (uint8_t *)malloc(1);
        out->prod_lens[0] = 0;
    }
    return 0;
}

static void free_manifest(ParsedManifest *m) {
    for (size_t i = 0; i < m->num_prods; i++) free(m->prods[i]);
    free(m->prods);
    free(m->prod_lens);
}

MrResult mr_run_ct_manifest(const char *manifest_path,
                            const char *input_bits,
                            const char *expected_final_tape,
                            size_t max_steps) {
    ParsedManifest m;
    if (parse_manifest(manifest_path, &m) != 0) {
        fprintf(stderr, "manifest load failed: %s\n", manifest_path);
        return MR_FAIL_LOAD;
    }
    size_t in_len;
    char *in_bytes = bit_string_to_bytes(input_bits, &in_len);

    CtState s;
    if (ct_init(&s, m.prods, m.prod_lens, m.num_prods,
                (uint8_t *)in_bytes, in_len, 8192) != 0) {
        free(in_bytes); free_manifest(&m); return MR_FAIL_LOAD;
    }
    CtHaltReason h = ct_run_until_halt(&s, max_steps);

    /* Compare final tape to expected. */
    size_t expected_len;
    char *expected_bytes = bit_string_to_bytes(expected_final_tape, &expected_len);

    MrResult result = MR_PASS;
    if (h != CT_HALT_EMPTY && h != CT_HALT_STEPLIMIT) {
        result = MR_FAIL_HALT_REASON;
    } else if (s.tape_len != expected_len ||
               memcmp(s.tape, expected_bytes, expected_len) != 0) {
        result = MR_FAIL_TAPE_MISMATCH;
        fprintf(stderr, "tape mismatch in %s: got len=%zu, expected len=%zu\n",
                manifest_path, s.tape_len, expected_len);
    }

    free(expected_bytes);
    free(in_bytes);
    ct_free(&s);
    free_manifest(&m);
    return result;
}
