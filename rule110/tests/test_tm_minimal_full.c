#include "cook_decode.h"
#include "cook_encode.h"
#include "cyclic_tag.h"
#include "rule110.h"
#include "tag_to_cyclic.h"
#include "tm_to_tag.h"

#include <assert.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define SMALL_TM_TAPE 8
#define TAG_TAPE_CAP 512
#define CYCLIC_TEXT_CAP 4096

static void configure_halted_tm(TMSpec *tm) {
    memset(tm, 0, sizeof(*tm));
    tm->num_states = 1;
    tm->num_symbols = 2;
    tm->halt_state = 0;
    for (int symbol = 0; symbol < 2; symbol++) {
        tm->transitions[0][symbol].write_symbol = symbol;
        tm->transitions[0][symbol].move = TM_MOVE_STAY;
        tm->transitions[0][symbol].next_state = 0;
    }
}

static void configure_write_one_tm(TMSpec *tm) {
    memset(tm, 0, sizeof(*tm));
    tm->num_states = 2;
    tm->num_symbols = 2;
    tm->halt_state = 1;

    tm->transitions[0][0].write_symbol = 1;
    tm->transitions[0][0].move = TM_MOVE_STAY;
    tm->transitions[0][0].next_state = 1;

    tm->transitions[0][1].write_symbol = 1;
    tm->transitions[0][1].move = TM_MOVE_STAY;
    tm->transitions[0][1].next_state = 1;

    for (int symbol = 0; symbol < 2; symbol++) {
        tm->transitions[1][symbol].write_symbol = symbol;
        tm->transitions[1][symbol].move = TM_MOVE_STAY;
        tm->transitions[1][symbol].next_state = 1;
    }
}

static int run_tm(const TMSpec *tm,
                  uint8_t *tape,
                  size_t tape_len,
                  int start_state,
                  int *out_state) {
    int state = start_state;
    size_t head = 0;

    for (size_t step = 0; step < 8; step++) {
        int read = 0;
        int move = 0;

        if (state == tm->halt_state) {
            *out_state = state;
            return 1;
        }
        if (head >= tape_len) return 0;
        read = tape[head];
        if (read < 0 || read >= tm->num_symbols) return 0;
        tape[head] = (uint8_t)tm->transitions[state][read].write_symbol;
        move = tm->transitions[state][read].move;
        state = tm->transitions[state][read].next_state;
        if (move == TM_MOVE_LEFT) {
            if (head == 0) return 0;
            head--;
        } else if (move == TM_MOVE_RIGHT) {
            head++;
            if (head >= tape_len) return 0;
        }
    }
    *out_state = state;
    return state == tm->halt_state;
}

static void cyclic_reference_text(const CyclicTagInput *cyclic,
                                  size_t steps,
                                  char *out,
                                  size_t out_cap) {
    CtState state;
    CtHaltReason halt;

    assert(ct_init(&state,
                   cyclic->productions,
                   cyclic->prod_lens,
                   cyclic->num_productions,
                   cyclic->initial_tape,
                   cyclic->tape_len,
                   cyclic->tape_len + 4096) == 0);
    halt = ct_run_until_halt(&state, steps);
    assert(halt != CT_HALT_OOM);
    assert(state.tape_len + 1 <= out_cap);
    for (size_t i = 0; i < state.tape_len; i++) {
        out[i] = state.tape[i] ? 'Y' : 'N';
    }
    out[state.tape_len] = '\0';
    ct_free(&state);
}

static void compile_tm(const TMSpec *tm,
                       const uint8_t *initial,
                       size_t initial_len,
                       int initial_state,
                       TagSystem *tag,
                       uint8_t *tag_tape,
                       size_t *tag_tape_len,
                       CyclicTagInput *cyclic) {
    assert(tm_to_tag(tm, tag));
    *tag_tape_len = TAG_TAPE_CAP;
    assert(tm_to_tag_initial_tape(tm,
                                  initial,
                                  initial_len,
                                  initial_state,
                                  tag_tape,
                                  tag_tape_len));
    assert(tag_to_cyclic(tag, tag_tape, *tag_tape_len, cyclic));
}

static void check_inverse_on_initial_tag_tape(const TMSpec *tm,
                                              const TagSystem *tag,
                                              const uint8_t *tm_initial,
                                              size_t tm_initial_len,
                                              const uint8_t *tag_tape,
                                              size_t tag_tape_len,
                                              const CyclicTagInput *cyclic) {
    char cyclic_text[CYCLIC_TEXT_CAP];
    uint8_t tag_back[TAG_TAPE_CAP];
    size_t tag_back_len = 0;
    uint8_t tm_back[SMALL_TM_TAPE];
    int state_back = -1;

    assert(cyclic->tape_len + 1 <= sizeof(cyclic_text));
    for (size_t i = 0; i < cyclic->tape_len; i++) {
        cyclic_text[i] = cyclic->initial_tape[i] ? 'Y' : 'N';
    }
    cyclic_text[cyclic->tape_len] = '\0';

    assert(cyclic_to_tag_inverse(tag,
                                 cyclic_text,
                                 tag_back,
                                 sizeof(tag_back),
                                 &tag_back_len));
    assert(tag_back_len == tag_tape_len);
    assert(memcmp(tag_back, tag_tape, tag_tape_len) == 0);

    assert(tag_to_tm_tape_inverse(tm,
                                  tag_back,
                                  tag_back_len,
                                  tm_back,
                                  sizeof(tm_back),
                                  &state_back));
    assert(state_back == 0);
    assert(memcmp(tm_back, tm_initial, tm_initial_len) == 0);
}

static void check_physical_gate(const CyclicTagInput *cyclic) {
    if (cyclic->num_productions <= 8 && cyclic->tape_len <= 32) {
        uint8_t placeholder = 0;
        uint8_t *cells = NULL;
        size_t written = 0;
        char decoded[CYCLIC_TEXT_CAP];
        int rc = cook_encode_phase_exact(cyclic, &placeholder, 0, &written);

        assert(rc == COOK_ENCODE_PHASE_EXACT_INSUFFICIENT_BUFFER);
        assert(written > 0);
        cells = (uint8_t *)malloc(written);
        assert(cells != NULL);
        rc = cook_encode_phase_exact(cyclic, cells, written, &written);
        assert(rc == COOK_ENCODE_PHASE_EXACT_OK);
        r110_run_n_steps(cells, written, 32768);
        rc = cook_decode_output(cells, written, decoded, sizeof(decoded));
        assert(rc == COOK_DECODE_OK);
        free(cells);
        return;
    }

    printf("  physical_rule110_gate: BLOCKED p=%zu t=%zu frontier_p=8 frontier_t=32\n",
           cyclic->num_productions,
           cyclic->tape_len);
}

static void test_halted_machine_frontier_floor(void) {
    TMSpec tm;
    TagSystem tag;
    CyclicTagInput cyclic;
    uint8_t tag_tape[TAG_TAPE_CAP];
    size_t tag_tape_len = 0;
    const uint8_t initial[1] = {0};

    configure_halted_tm(&tm);
    compile_tm(&tm, initial, sizeof(initial), 0, &tag, tag_tape, &tag_tape_len, &cyclic);
    assert(tag.num_alphabet == 16);
    assert(tag.s_deletion == 4);
    assert(cyclic.num_productions == 64);
    assert(cyclic.tape_len == 64);

    check_inverse_on_initial_tag_tape(&tm,
                                      &tag,
                                      initial,
                                      sizeof(initial),
                                      tag_tape,
                                      tag_tape_len,
                                      &cyclic);
    printf("  halted_tm_frontier_floor: PASS p=%zu t=%zu\n",
           cyclic.num_productions,
           cyclic.tape_len);
    check_physical_gate(&cyclic);
    cyclic_tag_input_free(&cyclic);
    tag_system_free(&tag);
}

static void test_write_one_tm_compile_and_reference(void) {
    TMSpec tm;
    TagSystem tag;
    CyclicTagInput cyclic;
    uint8_t tag_tape[TAG_TAPE_CAP];
    size_t tag_tape_len = 0;
    uint8_t tm_tape[SMALL_TM_TAPE] = {0, 0, 0, 0, 0, 0, 0, 0};
    const uint8_t expected[SMALL_TM_TAPE] = {1, 0, 0, 0, 0, 0, 0, 0};
    char cyclic_after[CYCLIC_TEXT_CAP];
    uint8_t tag_after[TAG_TAPE_CAP];
    size_t tag_after_len = 0;
    int final_state = -1;

    configure_write_one_tm(&tm);
    assert(run_tm(&tm, tm_tape, sizeof(tm_tape), 0, &final_state));
    assert(final_state == tm.halt_state);
    assert(memcmp(tm_tape, expected, sizeof(expected)) == 0);

    compile_tm(&tm,
               (const uint8_t[1]){0},
               1,
               0,
               &tag,
               tag_tape,
               &tag_tape_len,
               &cyclic);
    assert(tag.num_alphabet == 32);
    assert(tag.s_deletion == 4);
    assert(cyclic.num_productions == 128);
    assert(cyclic.tape_len == 128);

    cyclic_reference_text(&cyclic,
                          cyclic.tape_len,
                          cyclic_after,
                          sizeof(cyclic_after));
    assert(cyclic_to_tag_inverse(&tag,
                                 cyclic_after,
                                 tag_after,
                                 sizeof(tag_after),
                                 &tag_after_len));
    assert(tag_after_len == 4);
    for (size_t i = 0; i < tag_after_len; i++) {
        assert(tag_after[i] == (uint8_t)tm_tag_symbol_index(&tm,
                                                            TM_TAG_CLASS_HS,
                                                            0,
                                                            (int)i));
    }

    check_inverse_on_initial_tag_tape(&tm,
                                      &tag,
                                      (const uint8_t[1]){0},
                                      1,
                                      tag_tape,
                                      tag_tape_len,
                                      &cyclic);
    check_physical_gate(&cyclic);
    printf("  write_one_tm_compile_reference: PASS p=%zu t=%zu tag_final_len=%zu\n",
           cyclic.num_productions,
           cyclic.tape_len,
           tag_after_len);

    cyclic_tag_input_free(&cyclic);
    tag_system_free(&tag);
}

int main(void) {
    printf("== test_tm_minimal_full ==\n");
    test_halted_machine_frontier_floor();
    test_write_one_tm_compile_and_reference();
    printf("TM minimal full boundary: PASS\n");
    return 0;
}
