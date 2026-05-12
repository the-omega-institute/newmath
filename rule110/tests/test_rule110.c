#include "rule110.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static void test_single_step_known_pattern(void) {
    /* Rule 110: input neighborhood (left,self,right) -> next.
       Truth table {0,1,1,1,0,1,1,0} (indexed by left*4+self*2+right). */
    uint8_t cells[8] = {0,0,0,1,0,0,0,0};  /* single 1 at index 3 */
    r110_step(cells, 8);
    /* expected: neighbors of position 3 (left=0,self=1,right=0 -> idx 010 = 2 -> table[2]=1).
       position 2: (0,0,1) -> idx 001 = 1 -> table[1]=1.
       position 3 stays 1, position 4 (1,0,0) -> idx 100 = 4 -> table[4]=0. */
    uint8_t expected[8] = {0,0,1,1,0,0,0,0};
    for (int i = 0; i < 8; i++) assert(cells[i] == expected[i]);
    printf("  single_step_known_pattern: PASS\n");
}

static void test_all_zero_stays_zero(void) {
    uint8_t cells[10] = {0};
    r110_run_n_steps(cells, 10, 100);
    for (int i = 0; i < 10; i++) assert(cells[i] == 0);
    printf("  all_zero_stays_zero: PASS\n");
}

static void test_boundary_fixed_at_zero(void) {
    /* single 1 at leftmost position; left neighbor (off-grid) treated as 0. */
    uint8_t cells[5] = {1,0,0,0,0};
    r110_step(cells, 5);
    /* position 0: (off=0, self=1, right=0) -> idx 010=2 -> table[2]=1.
       position 1: (left=1, self=0, right=0) -> idx 100=4 -> table[4]=0.
       position 2..4: all (0,0,0) -> table[0]=0. */
    uint8_t expected[5] = {1,0,0,0,0};
    for (int i = 0; i < 5; i++) assert(cells[i] == expected[i]);
    printf("  boundary_fixed_at_zero: PASS\n");
}

static void test_dump_state_format(void) {
    uint8_t cells[4] = {0,1,1,0};
    char buf[16] = {0};
    FILE *m = fmemopen(buf, sizeof(buf), "w");
    if (!m) { /* fmemopen may not be ANSI; if absent, use a temp file. Skip on portability. */
        printf("  dump_state_format: SKIP (fmemopen unavailable)\n");
        return;
    }
    r110_dump_state(cells, 4, m);
    fclose(m);
    assert(strncmp(buf, "0110\n", 5) == 0);
    printf("  dump_state_format: PASS\n");
}

int main(void) {
    printf("== test_rule110 ==\n");
    test_single_step_known_pattern();
    test_all_zero_stays_zero();
    test_boundary_fixed_at_zero();
    test_dump_state_format();
    printf("ALL test_rule110 tests passed\n");
    return 0;
}
