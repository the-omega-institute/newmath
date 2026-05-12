#include "cook_construction.h"
#include "cook_data_block.h"
#include "cook_encode.h"
#include "cook_leader.h"
#include "cook_ossifier.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define ARB_LEADER_POS 100
#define ARB_FIRST_OSSIFIER_POS 300
#define ARB_OSSIFIER_STRIDE 200
#define ARB_ZERO_DATA_BLOCK_POS 800
#define ARB_DATA_GAP 500

#define MAX_MANIFEST_PRODUCTIONS 16
#define MAX_MANIFEST_LINE 512
#define MAX_TAPE_BITS 128

typedef struct {
    uint8_t *productions[MAX_MANIFEST_PRODUCTIONS];
    size_t prod_lens[MAX_MANIFEST_PRODUCTIONS];
    uint8_t tape[MAX_TAPE_BITS];
    size_t num_productions;
    size_t tape_len;
} ManifestCase;

static size_t count_different(const uint8_t *left,
                              const uint8_t *right,
                              size_t lo,
                              size_t hi) {
    size_t count = 0;

    for (size_t i = lo; i < hi; i++) {
        if (left[i] != right[i]) count++;
    }

    return count;
}

static void assert_ether_range(const uint8_t *cells,
                               size_t lo,
                               size_t hi) {
    for (size_t i = lo; i < hi; i++) {
        assert(cells[i] == COOK_ETHER_PATTERN[i % COOK_ETHER_WIDTH]);
    }
}

static void assert_region_changed(const uint8_t *cells,
                                  const uint8_t *ether,
                                  size_t pos,
                                  size_t width) {
    assert(count_different(cells, ether, pos, pos + width) > 0);
}

static uint8_t *dup_bits(const char *text, size_t len) {
    uint8_t *bits = NULL;

    if (len == 0) return NULL;

    bits = (uint8_t *)malloc(len);
    assert(bits != NULL);
    for (size_t i = 0; i < len; i++) {
        assert(text[i] == '0' || text[i] == '1');
        bits[i] = (uint8_t)(text[i] == '1' ? 1 : 0);
    }

    return bits;
}

static size_t bit_prefix_len(const char *text) {
    size_t len = 0;

    while (text[len] == '0' || text[len] == '1') len++;

    return len;
}

static void trim_newline(char *text) {
    size_t len = strlen(text);

    while (len > 0 && (text[len - 1] == '\n' || text[len - 1] == '\r')) {
        text[len - 1] = '\0';
        len--;
    }
}

static int parse_first_input(const char *line,
                             uint8_t *tape,
                             size_t *tape_len) {
    const char needle[] = "input=";
    char *start = strstr(line, needle);
    size_t len = 0;

    if (start == NULL) return 0;
    start += sizeof(needle) - 1;
    len = bit_prefix_len(start);
    assert(len <= MAX_TAPE_BITS);
    for (size_t i = 0; i < len; i++) {
        tape[i] = (uint8_t)(start[i] == '1' ? 1 : 0);
    }
    *tape_len = len;

    return 1;
}

static void manifest_case_free(ManifestCase *mc) {
    for (size_t i = 0; i < mc->num_productions; i++) {
        free(mc->productions[i]);
        mc->productions[i] = NULL;
    }
}

static void read_manifest_case(const char *path, ManifestCase *out) {
    FILE *f = fopen(path, "r");
    char line[MAX_MANIFEST_LINE];
    size_t expected_productions = 0;
    size_t production_index = 0;
    int in_productions = 0;
    int saw_input = 0;

    assert(f != NULL);
    memset(out, 0, sizeof(*out));

    while (fgets(line, sizeof(line), f) != NULL) {
        trim_newline(line);
        if (strncmp(line, "PRODUCTIONS ", 12) == 0) {
            expected_productions = (size_t)strtoul(line + 12, NULL, 10);
            assert(expected_productions <= MAX_MANIFEST_PRODUCTIONS);
            out->num_productions = expected_productions;
            production_index = 0;
            in_productions = 1;
            continue;
        }
        if (strncmp(line, "ASSERTIONS ", 11) == 0) {
            in_productions = 0;
            continue;
        }
        if (in_productions) {
            size_t len = bit_prefix_len(line);

            assert(out->num_productions == expected_productions);
            assert(len == strlen(line));
            assert(production_index < expected_productions);
            out->prod_lens[production_index] = len;
            out->productions[production_index] = dup_bits(line, len);
            production_index++;
            continue;
        }
        if (!saw_input && parse_first_input(line, out->tape, &out->tape_len)) {
            saw_input = 1;
        }
    }

    assert(fclose(f) == 0);
    assert(production_index == expected_productions);
    assert(saw_input);
}

static void test_two_productions_empty_tape(void) {
    uint8_t p0[2] = {1, 0};
    uint8_t p1[3] = {0, 1, 1};
    uint8_t *productions[2] = {p0, p1};
    size_t prod_lens[2] = {2, 3};
    CyclicTagInput ct = {productions, prod_lens, 2, NULL, 0};
    uint8_t *cells = (uint8_t *)malloc(8192);
    uint8_t *ether = (uint8_t *)malloc(8192);
    size_t written = 0;
    size_t p0_width = prod_lens[0] * COOK_OSSIFIER_WIDTH_PER_BIT;
    size_t p1_width = prod_lens[1] * COOK_OSSIFIER_WIDTH_PER_BIT;

    assert(cells != NULL);
    assert(ether != NULL);

    written = cook_encode(&ct, cells, 8192);
    assert(written > 0);
    assert(written <= 8192);

    cook_ether_emit(ether, written / COOK_ETHER_WIDTH);
    assert_region_changed(cells, ether, ARB_LEADER_POS, COOK_LEADER_WIDTH);
    assert_region_changed(cells, ether, ARB_FIRST_OSSIFIER_POS, p0_width);
    assert_region_changed(cells, ether,
                          ARB_FIRST_OSSIFIER_POS + ARB_OSSIFIER_STRIDE,
                          p1_width);
    assert_ether_range(cells,
                       ARB_FIRST_OSSIFIER_POS + p0_width,
                       ARB_FIRST_OSSIFIER_POS + ARB_OSSIFIER_STRIDE);
    assert_ether_range(cells,
                       ARB_FIRST_OSSIFIER_POS + ARB_OSSIFIER_STRIDE + p1_width,
                       written);

    free(ether);
    free(cells);
    printf("  two_productions_empty_tape: PASS\n");
}

static void test_two_productions_five_bit_tape(void) {
    uint8_t p0[1] = {1};
    uint8_t p1[2] = {0, 1};
    uint8_t *productions[2] = {p0, p1};
    size_t prod_lens[2] = {1, 2};
    uint8_t tape[5] = {1, 0, 1, 1, 0};
    CyclicTagInput ct = {productions, prod_lens, 2, tape, 5};
    uint8_t *cells = (uint8_t *)malloc(8192);
    uint8_t *ether = (uint8_t *)malloc(8192);
    size_t written = 0;
    size_t data_pos = ARB_FIRST_OSSIFIER_POS +
        (2 * ARB_OSSIFIER_STRIDE) + ARB_DATA_GAP;
    size_t data_width = 5 * COOK_DATA_BLOCK_WIDTH_PER_BIT;

    assert(cells != NULL);
    assert(ether != NULL);

    written = cook_encode(&ct, cells, 8192);
    assert(written > 0);
    assert(written <= 8192);

    cook_ether_emit(ether, written / COOK_ETHER_WIDTH);
    assert_region_changed(cells, ether, ARB_LEADER_POS, COOK_LEADER_WIDTH);
    assert_region_changed(cells, ether,
                          ARB_FIRST_OSSIFIER_POS,
                          prod_lens[0] * COOK_OSSIFIER_WIDTH_PER_BIT);
    assert_region_changed(cells, ether,
                          ARB_FIRST_OSSIFIER_POS + ARB_OSSIFIER_STRIDE,
                          prod_lens[1] * COOK_OSSIFIER_WIDTH_PER_BIT);
    assert_region_changed(cells, ether, data_pos, data_width);
    assert_ether_range(cells,
                       ARB_FIRST_OSSIFIER_POS +
                       ARB_OSSIFIER_STRIDE +
                       (prod_lens[1] * COOK_OSSIFIER_WIDTH_PER_BIT),
                       data_pos);

    free(ether);
    free(cells);
    printf("  two_productions_five_bit_tape: PASS\n");
}

static void test_four_productions_three_bit_tape(void) {
    uint8_t p0[1] = {1};
    uint8_t p1[2] = {1, 0};
    uint8_t p2[3] = {0, 1, 0};
    uint8_t p3[1] = {0};
    uint8_t *productions[4] = {p0, p1, p2, p3};
    size_t prod_lens[4] = {1, 2, 3, 1};
    uint8_t tape[3] = {0, 1, 1};
    CyclicTagInput ct = {productions, prod_lens, 4, tape, 3};
    uint8_t *cells = (uint8_t *)malloc(8192);
    uint8_t *ether = (uint8_t *)malloc(8192);
    size_t written = 0;
    size_t data_pos = ARB_FIRST_OSSIFIER_POS +
        (4 * ARB_OSSIFIER_STRIDE) + ARB_DATA_GAP;

    assert(cells != NULL);
    assert(ether != NULL);

    written = cook_encode(&ct, cells, 8192);
    assert(written > 0);
    assert(written <= 8192);

    cook_ether_emit(ether, written / COOK_ETHER_WIDTH);
    assert_region_changed(cells, ether, ARB_LEADER_POS, COOK_LEADER_WIDTH);
    for (size_t i = 0; i < 4; i++) {
        assert_region_changed(cells,
                              ether,
                              ARB_FIRST_OSSIFIER_POS +
                              (i * ARB_OSSIFIER_STRIDE),
                              prod_lens[i] * COOK_OSSIFIER_WIDTH_PER_BIT);
    }
    assert_region_changed(cells,
                          ether,
                          data_pos,
                          3 * COOK_DATA_BLOCK_WIDTH_PER_BIT);

    free(ether);
    free(cells);
    printf("  four_productions_three_bit_tape: PASS\n");
}

static void test_mark_manifest_productions(void) {
    static const char *paths[8] = {
        "manifests/mark/msame_refl.enum.ct",
        "manifests/mark/msame_refl.algo.ct",
        "manifests/mark/msame_symm.enum.ct",
        "manifests/mark/msame_symm.algo.ct",
        "manifests/mark/msame_trans.enum.ct",
        "manifests/mark/msame_trans.algo.ct",
        "manifests/mark/msame_no_confusion.enum.ct",
        "manifests/mark/msame_no_confusion.algo.ct"
    };

    for (size_t i = 0; i < 8; i++) {
        ManifestCase mc;
        CyclicTagInput ct;
        uint8_t *cells = (uint8_t *)malloc(8192);
        size_t written = 0;

        assert(cells != NULL);
        read_manifest_case(paths[i], &mc);

        ct.productions = mc.productions;
        ct.prod_lens = mc.prod_lens;
        ct.num_productions = mc.num_productions;
        ct.initial_tape = mc.tape;
        ct.tape_len = mc.tape_len;

        written = cook_encode(&ct, cells, 8192);
        assert(written > 0);
        assert(written <= 8192);

        free(cells);
        manifest_case_free(&mc);
    }

    printf("  mark_manifest_productions: PASS\n");
}

int main(void) {
    printf("== test_cook_encode_arbitrary ==\n");
    test_two_productions_empty_tape();
    test_two_productions_five_bit_tape();
    test_four_productions_three_bit_tape();
    test_mark_manifest_productions();
    printf("ALL test_cook_encode_arbitrary tests passed\n");
    return 0;
}
