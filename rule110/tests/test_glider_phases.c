#include "glider_phases.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

static void test_catalog_lookup(void) {
    size_t len = 0;
    const char *bits = glider_phase("A", NULL, 1, &len);

    assert(bits != NULL);
    assert(strcmp(bits, "111110") == 0);
    assert(len == 6);

    bits = glider_phase("Ebar", "A", 1, &len);
    assert(bits != NULL);
    assert(strcmp(bits, "111110000100011111010") == 0);
    assert(len == 21);

    bits = glider_phase("E-", "A", 1, &len);
    assert(bits != NULL);
    assert(strcmp(bits, "111110000100011111010") == 0);
    assert(len == 21);

    bits = glider_phase("D1", "A", 1, &len);
    assert(bits != NULL);
    assert(strcmp(bits, "11111000010") == 0);
    assert(len == 11);

    bits = glider_phase("D1", "B", 4, &len);
    assert(bits != NULL);
    assert(strcmp(bits, "11111011100") == 0);
    assert(len == 11);

    bits = glider_phase("D1", "C", 4, &len);
    assert(bits != NULL);
    assert(strcmp(bits, "11111000010") == 0);
    assert(len == 11);

    bits = glider_phase("D2", "A", 1, &len);
    assert(bits != NULL);
    assert(strcmp(bits, "1111101011000100110") == 0);
    assert(len == 19);

    bits = glider_phase("D2", "B", 3, &len);
    assert(bits != NULL);
    assert(strcmp(bits, "111110001001101110111111000100110") == 0);
    assert(len == 33);

    bits = glider_phase("D2", "C", 4, &len);
    assert(bits != NULL);
    assert(strcmp(bits, "1111101011000100110") == 0);
    assert(len == 19);

    assert(glider_phase("D", "A", 1, &len) == NULL);

    printf("  catalog_lookup: PASS\n");
}

static void test_catalog_emit(void) {
    uint8_t cells[32] = {0};
    size_t written = 0;
    int rc = glider_phase_emit(cells, 3, sizeof(cells),
                               "B", NULL, 1, &written);

    assert(rc == 0);
    assert(written == 8);
    assert(cells[3] == 1);
    assert(cells[4] == 1);
    assert(cells[5] == 1);
    assert(cells[6] == 1);
    assert(cells[7] == 1);
    assert(cells[8] == 0);
    assert(cells[9] == 1);
    assert(cells[10] == 0);

    printf("  catalog_emit: PASS\n");
}

int main(void) {
    printf("== test_glider_phases ==\n");
    test_catalog_lookup();
    test_catalog_emit();
    printf("ALL test_glider_phases tests passed\n");
    return 0;
}
