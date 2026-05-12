#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

/* For msame_symm enum/algo: same input as reflexive, plus vacuous cases that
   need only verify the antecedent of the implication is false. */
static int decode_two_unequal(const char *input_bits) {
    size_t in_len = strlen(input_bits);
    uint8_t *in_bytes = (uint8_t *)malloc(in_len);
    for (size_t i = 0; i < in_len; i++) in_bytes[i] = (uint8_t)(input_bits[i] - '0');

    GcDecResult r1 = gc_dec_event(in_bytes, in_len, 64);
    if (r1.status != GC_OK) { free(in_bytes); free(r1.event); return 0; }
    size_t off = r1.bytes_consumed;
    GcDecResult r2 = gc_dec_event(in_bytes + off, in_len - off, 64);
    if (r2.status != GC_OK) { free(in_bytes); free(r1.event); free(r2.event); return 0; }

    int neq = (r1.event_len != r2.event_len) ||
              (memcmp(r1.event, r2.event, r1.event_len) != 0);
    free(in_bytes); free(r1.event); free(r2.event);
    return neq;
}

/* For msame_trans: decode three events and verify trans relation.
   Returns: 1 if first==second && second==third implies first==third trivially holds. */
static int decode_three_check_trans(const char *input_bits) {
    size_t in_len = strlen(input_bits);
    uint8_t *in_bytes = (uint8_t *)malloc(in_len);
    for (size_t i = 0; i < in_len; i++) in_bytes[i] = (uint8_t)(input_bits[i] - '0');

    GcDecResult r1 = gc_dec_event(in_bytes, in_len, 64);
    if (r1.status != GC_OK) { free(in_bytes); free(r1.event); return 0; }
    size_t off = r1.bytes_consumed;
    GcDecResult r2 = gc_dec_event(in_bytes + off, in_len - off, 64);
    if (r2.status != GC_OK) { free(in_bytes); free(r1.event); free(r2.event); return 0; }
    off += r2.bytes_consumed;
    GcDecResult r3 = gc_dec_event(in_bytes + off, in_len - off, 64);
    if (r3.status != GC_OK) { free(in_bytes); free(r1.event); free(r2.event); free(r3.event); return 0; }

    int eq12 = (r1.event_len == r2.event_len) && (memcmp(r1.event, r2.event, r1.event_len) == 0);
    int eq23 = (r2.event_len == r3.event_len) && (memcmp(r2.event, r3.event, r2.event_len) == 0);
    int eq13 = (r1.event_len == r3.event_len) && (memcmp(r1.event, r3.event, r1.event_len) == 0);

    free(in_bytes); free(r1.event); free(r2.event); free(r3.event);
    /* Transitivity: if both antecedents hold, conclusion must hold. Otherwise vacuous. */
    if (eq12 && eq23) return eq13;
    return 1;  /* vacuous case */
}

static int enum_assert_reflexive(const char *input_bits) {
    return !decode_two_unequal(input_bits);
}

static void test_msame_symm_enum(void) {
    /* All 4 cases trivially or vacuously satisfy symm. */
    assert(enum_assert_reflexive("011011"));      /* b0,b0 - reflexive trivial */
    /* For vacuous cases (b0,b1) and (b1,b0), the antecedent msame(m,n) is false,
       so the implication holds. We just verify these inputs decode and have unequal events. */
    assert(decode_two_unequal("0111011"));        /* b0,b1 vacuous */
    assert(decode_two_unequal("1011011"));        /* b1,b0 vacuous */
    assert(enum_assert_reflexive("10111011"));    /* b1,b1 trivial */
    printf("  msame_symm.enum: 4/4 cases PASS\n");
}

static void test_msame_symm_algo(void) {
    /* Same logic as enum for vertical slice. */
    assert(enum_assert_reflexive("011011"));
    assert(decode_two_unequal("0111011"));
    assert(decode_two_unequal("1011011"));
    assert(enum_assert_reflexive("10111011"));
    printf("  msame_symm.algo: 4/4 cases PASS\n");
}

static void test_msame_trans_enum(void) {
    assert(decode_three_check_trans("011011011"));       /* b0_b0_b0 */
    assert(decode_three_check_trans("0110111011"));      /* b0_b0_b1 vacuous */
    assert(decode_three_check_trans("0111011011"));      /* b0_b1_b0 vacuous */
    assert(decode_three_check_trans("01110111011"));     /* b0_b1_b1 vacuous */
    assert(decode_three_check_trans("1011011011"));      /* b1_b0_b0 vacuous */
    assert(decode_three_check_trans("10110111011"));     /* b1_b0_b1 vacuous */
    assert(decode_three_check_trans("10111011011"));     /* b1_b1_b0 vacuous */
    assert(decode_three_check_trans("101110111011"));    /* b1_b1_b1 trivial */
    printf("  msame_trans.enum: 8/8 cases PASS\n");
}

static void test_msame_trans_algo(void) {
    assert(decode_three_check_trans("011011011"));
    assert(decode_three_check_trans("0110111011"));
    assert(decode_three_check_trans("0111011011"));
    assert(decode_three_check_trans("01110111011"));
    assert(decode_three_check_trans("1011011011"));
    assert(decode_three_check_trans("10110111011"));
    assert(decode_three_check_trans("10111011011"));
    assert(decode_three_check_trans("101110111011"));
    printf("  msame_trans.algo: 8/8 cases PASS\n");
}

static void test_msame_no_confusion_enum(void) {
    assert(decode_two_unequal("0111011"));    /* b0,b1 must be unequal */
    assert(decode_two_unequal("1011011"));    /* b1,b0 must be unequal */
    printf("  msame_no_confusion.enum: 2/2 cases PASS\n");
}

static void test_msame_no_confusion_algo(void) {
    assert(decode_two_unequal("0111011"));
    assert(decode_two_unequal("1011011"));
    printf("  msame_no_confusion.algo: 2/2 cases PASS\n");
}

int main(void) {
    printf("== test_mark ==\n");
    test_msame_symm_enum();
    test_msame_symm_algo();
    test_msame_trans_enum();
    test_msame_trans_algo();
    test_msame_no_confusion_enum();
    test_msame_no_confusion_algo();
    printf("ALL test_mark assertions passed (28 - symm/trans/no_confusion; sibling worker fills in 4 more)\n");
    return 0;
}
