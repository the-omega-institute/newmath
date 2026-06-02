#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/wait.h>

#define WORD_LEN 18u
#define EXPECTED_WORDS 21u
#define TSV "experiments/zeckendorf_projection/words_18.tsv"
#define TOOL "./tools/r110_zeckendorf_projection"

static uint32_t parse_word(const char *s) {
    uint32_t key = 0;
    assert(strlen(s) == WORD_LEN);
    for (size_t i = 0; i < WORD_LEN; i++) {
        assert(s[i] == '0' || s[i] == '1');
        key = (key << 1) | (uint32_t)(s[i] == '1');
    }
    return key;
}

static int has_11(uint32_t key) {
    return (key & (key >> 1)) != 0u;
}

static int run_tool(void) {
    return system(TOOL " > /tmp/r110_zeckendorf_projection.out 2> /tmp/r110_zeckendorf_projection.err");
}

static int file_exists(const char *path) {
    FILE *f = fopen(path, "r");
    if (f == NULL) return 0;
    fclose(f);
    return 1;
}

static int file_contains(const char *path, const char *needle) {
    FILE *f = fopen(path, "r");
    char buf[1024];
    if (f == NULL) return 0;
    while (fgets(buf, sizeof(buf), f) != NULL) {
        if (strstr(buf, needle) != NULL) {
            fclose(f);
            return 1;
        }
    }
    fclose(f);
    return 0;
}

static int validate_tsv(const char *path) {
    FILE *f = fopen(path, "r");
    char line[2048];
    uint32_t keys[EXPECTED_WORDS];
    size_t rows = 0;
    if (f == NULL) return 0;
    if (fgets(line, sizeof(line), f) == NULL) return 0;
    line[strcspn(line, "\r\n")] = '\0';
    if (strcmp(line, "word\tlength\tsource_mode\tsource_manifest\tsource_case\tsource_time\tdecoded_window_start\tdecoded_window_end\tsymbol_map\tcontains_11\taccepted") != 0) return 0;
    while (fgets(line, sizeof(line), f) != NULL) {
        char *fields[11];
        char *cursor = line;
        uint32_t key;
        line[strcspn(line, "\r\n")] = '\0';
        for (size_t i = 0; i < 11; i++) {
            fields[i] = cursor;
            cursor = strchr(cursor, '\t');
            if (i < 10) {
                if (cursor == NULL) return 0;
                *cursor++ = '\0';
            } else {
                if (cursor != NULL) return 0;
            }
        }
        if (strcmp(fields[1], "18") != 0 ||
            strcmp(fields[2], "cook_decoded_symbol_window") != 0 ||
            strstr(fields[3], ".algo.r110.ct") == NULL ||
            strcmp(fields[8], "N0_Y1") != 0 ||
            strcmp(fields[9], "false") != 0 ||
            strcmp(fields[10], "true") != 0) return 0;
        key = parse_word(fields[0]);
        if (has_11(key) || rows >= EXPECTED_WORDS) return 0;
        for (size_t i = 0; i < rows; i++) if (keys[i] == key) return 0;
        keys[rows++] = key;
    }
    fclose(f);
    return rows == EXPECTED_WORDS;
}

static void require_bad_tsv_rejected(void) {
    FILE *f = fopen("/tmp/r110_zeckendorf_bad.tsv", "w");
    assert(f != NULL);
    fprintf(f, "word\tlength\tsource_mode\tsource_manifest\tsource_case\tsource_time\tdecoded_window_start\tdecoded_window_end\tsymbol_map\tcontains_11\taccepted\n");
    fprintf(f, "000000000000000000\t18\tdirect_payload\tmanifests/ask/ask_basic.r110.ct\tcase\t1\t0\t18\tN0_Y1\tfalse\ttrue\n");
    fclose(f);
    assert(!validate_tsv("/tmp/r110_zeckendorf_bad.tsv"));
}

static void require_fixed_row_negative(void) {
    FILE *f = fopen("/tmp/r110_zeckendorf_projection.out", "r");
    char buf[512];
    size_t baseline = 0;
    assert(f != NULL);
    assert(fgets(buf, sizeof(buf), f) != NULL);
    fclose(f);
    assert(sscanf(buf,
                  "cook_decoded_unique=%*zu replay_cases=%*zu decoded_cases=%*zu fixed_row_step1_unique=%zu",
                  &baseline) == 1);
    assert(baseline != EXPECTED_WORDS);
}

static void require_fail_closed_projection(void) {
    int rc = run_tool();
    assert(rc != -1);
    assert(WIFEXITED(rc));
    assert(WEXITSTATUS(rc) != 0);
    assert(file_contains("/tmp/r110_zeckendorf_projection.out", "cook_decoded_unique=0"));
    assert(file_contains("/tmp/r110_zeckendorf_projection.out", "fixed_row_step1_unique=18"));
    assert(file_contains("/tmp/r110_zeckendorf_projection.err",
                         "reject: Cook decoded unique count is 0, expected 21"));
    assert(!file_exists(TSV));
}

int main(void) {
    require_fail_closed_projection();
    require_bad_tsv_rejected();
    require_fixed_row_negative();
    printf("ALL test_r110_zeckendorf_projection tests passed\n");
    return 0;
}
