#include "cook_construction.h"
#include "cook_encode.h"
#include "cook_leader.h"
#include "rule110.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <string.h>

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

static void test_cook_encode_empty(void) {
    CyclicTagInput ct = {NULL, NULL, 0, NULL, 0};
    uint8_t buf[2048] = {0};
    uint8_t ether[2048] = {0};
    const size_t leader_pos = 100;
    const size_t window_lo = leader_pos - (2 * COOK_LEADER_WIDTH);
    const size_t window_hi = leader_pos + (3 * COOK_LEADER_WIDTH);
    size_t written = cook_encode(&ct, buf, sizeof(buf));
    size_t changed = 0;

    assert(written == 50 * (size_t)COOK_ETHER_WIDTH);

    cook_ether_emit(ether, 50);
    r110_run_n_steps(buf, written, COOK_LEADER_STABILITY_STEPS);
    r110_run_n_steps(ether, written, COOK_LEADER_STABILITY_STEPS);

    changed = count_different(buf, ether, window_lo, window_hi);
    assert(changed > 0);

    printf("  cook_encode_empty: PASS\n");
}

static void test_cook_encode_empty_rejects_small_buffer(void) {
    CyclicTagInput ct = {NULL, NULL, 0, NULL, 0};
    uint8_t buf[128] = {0};
    size_t written = cook_encode(&ct, buf, sizeof(buf));

    assert(written == 0);

    printf("  cook_encode_empty_rejects_small_buffer: PASS\n");
}

static void test_cook_encode_non_empty_stub(void) {
    uint8_t bit = 1;
    uint8_t *productions[1] = {&bit};
    size_t prod_lens[1] = {1};
    CyclicTagInput ct = {productions, prod_lens, 1, NULL, 0};
    uint8_t buf[2048] = {0};
    size_t written = cook_encode(&ct, buf, sizeof(buf));

    assert(written == 0);

    printf("  cook_encode_non_empty_stub: PASS\n");
}

int main(void) {
    printf("== test_cook_encode_empty ==\n");
    test_cook_encode_empty();
    test_cook_encode_empty_rejects_small_buffer();
    test_cook_encode_non_empty_stub();
    printf("ALL test_cook_encode_empty tests passed\n");
    return 0;
}
