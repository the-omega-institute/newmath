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

#define PILOT_TAPE_LEN 3
#define TAG_TAPE_CAP 4096
#define DECODE_BUF 4096

static char *alloc_rule(const uint8_t *symbols, size_t len) {
    char *out = (char *)malloc(len ? len : 1);

    assert(out != NULL);
    if (len > 0) memcpy(out, symbols, len);
    return out;
}

static void configure_increment_tm(TMSpec *tm) {
    memset(tm, 0, sizeof(*tm));
    tm->num_states = 3;
    tm->num_symbols = 2;
    tm->halt_state = 2;

    tm->transitions[0][0].write_symbol = 1;
    tm->transitions[0][0].move = TM_MOVE_RIGHT;
    tm->transitions[0][0].next_state = 1;

    tm->transitions[0][1].write_symbol = 0;
    tm->transitions[0][1].move = TM_MOVE_RIGHT;
    tm->transitions[0][1].next_state = 0;

    tm->transitions[1][0].write_symbol = 1;
    tm->transitions[1][0].move = TM_MOVE_STAY;
    tm->transitions[1][0].next_state = 2;

    tm->transitions[1][1].write_symbol = 1;
    tm->transitions[1][1].move = TM_MOVE_LEFT;
    tm->transitions[1][1].next_state = 1;

    for (int symbol = 0; symbol < 2; symbol++) {
        tm->transitions[2][symbol].write_symbol = symbol;
        tm->transitions[2][symbol].move = TM_MOVE_STAY;
        tm->transitions[2][symbol].next_state = 2;
    }
}

static int run_tm(const TMSpec *tm,
                  uint8_t *tape,
                  size_t tape_len,
                  int start_state,
                  size_t max_steps) {
    int state = start_state;
    size_t head = 0;

    for (size_t step = 0; step < max_steps; step++) {
        int read = 0;
        int move = 0;

        if (state == tm->halt_state) return 1;
        assert(head < tape_len);
        read = tape[head];
        assert(read >= 0 && read < tm->num_symbols);
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
    return state == tm->halt_state;
}

static void run_cyclic_reference(const CyclicTagInput *cyclic,
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
                   cyclic->tape_len + 8192) == 0);
    halt = ct_run_until_halt(&state, steps);
    assert(halt != CT_HALT_OOM);
    assert(state.tape_len + 1 <= out_cap);
    for (size_t i = 0; i < state.tape_len; i++) {
        out[i] = state.tape[i] ? 'Y' : 'N';
    }
    out[state.tape_len] = '\0';
    ct_free(&state);
}

static size_t decode_unary_tag_tape(const char *decoded,
                                    size_t alphabet,
                                    uint8_t *out,
                                    size_t out_cap) {
    size_t decoded_len = strlen(decoded);
    size_t count = 0;

    assert(alphabet > 0);
    assert(decoded_len % alphabet == 0);
    assert(decoded_len / alphabet <= out_cap);
    for (size_t pos = 0; pos < decoded_len; pos += alphabet) {
        size_t found = alphabet;

        for (size_t i = 0; i < alphabet; i++) {
            assert(decoded[pos + i] == 'N' || decoded[pos + i] == 'Y');
            if (decoded[pos + i] == 'Y') {
                assert(found == alphabet);
                found = i;
            }
        }
        assert(found < alphabet);
        out[count++] = (uint8_t)found;
    }
    return count;
}

static void test_tm_to_tag_pipeline_surface(void) {
    TMSpec tm;
    TagSystem tag;
    CyclicTagInput cyclic;
    uint8_t tm_tape[PILOT_TAPE_LEN] = {0, 0, 0};
    const uint8_t expected[PILOT_TAPE_LEN] = {1, 1, 0};
    uint8_t tag_tape[TAG_TAPE_CAP];
    size_t tag_tape_cap = sizeof(tag_tape);

    configure_increment_tm(&tm);
    assert(run_tm(&tm, tm_tape, PILOT_TAPE_LEN, 0, 16));
    assert(memcmp(tm_tape, expected, sizeof(expected)) == 0);

    assert(tm_to_tag(&tm, &tag));
    assert(tag.num_alphabet == 48);
    assert(tag.s_deletion == 4);
    assert(tag.num_rules == 48);
    assert(tm_to_tag_initial_tape(&tm,
                                  (const uint8_t[PILOT_TAPE_LEN]){0, 0, 0},
                                  PILOT_TAPE_LEN,
                                  0,
                                  tag_tape,
                                  &tag_tape_cap));
    assert(tag_tape_cap == 64);

    assert(tag_to_cyclic(&tag, tag_tape, tag_tape_cap, &cyclic));
    assert(cyclic.num_productions == 192);
    assert(cyclic.tape_len == 3072);

    cyclic_tag_input_free(&cyclic);
    tag_system_free(&tag);
    printf("  tm_to_tag_pipeline_surface: PASS\n");
}

static void test_compact_tag_to_rule110_round_trip(void) {
    TagSystem tag;
    CyclicTagInput cyclic;
    uint8_t tag_initial[2] = {0, 1};
    uint8_t tag_decoded[2];
    uint8_t r0[1] = {1};
    uint8_t r1[2] = {0, 1};
    char expected[DECODE_BUF];
    char decoded[DECODE_BUF];
    uint8_t placeholder = 0;
    uint8_t *cells = NULL;
    size_t written = 0;
    int rc = 0;
    size_t tag_len = 0;

    memset(&tag, 0, sizeof(tag));
    tag.num_alphabet = 2;
    tag.s_deletion = 2;
    tag.num_rules = 2;
    tag.rules[0].appendant = alloc_rule(r0, sizeof(r0));
    tag.rules[0].appendant_len = sizeof(r0);
    tag.rules[1].appendant = alloc_rule(r1, sizeof(r1));
    tag.rules[1].appendant_len = sizeof(r1);

    assert(tag_to_cyclic(&tag, tag_initial, sizeof(tag_initial), &cyclic));
    run_cyclic_reference(&cyclic, cyclic.tape_len, expected, sizeof(expected));

    rc = cook_encode_phase_exact(&cyclic, &placeholder, 0, &written);
    assert(rc == COOK_ENCODE_PHASE_EXACT_INSUFFICIENT_BUFFER);
    assert(written > 0);
    cells = (uint8_t *)malloc(written);
    assert(cells != NULL);
    rc = cook_encode_phase_exact(&cyclic, cells, written, &written);
    assert(rc == COOK_ENCODE_PHASE_EXACT_OK);

    r110_run_n_steps(cells, written, 1024);
    rc = cook_decode_output(cells, written, decoded, sizeof(decoded));
    assert(rc == COOK_DECODE_OK);
    assert(strcmp(decoded, expected) == 0);

    tag_len = decode_unary_tag_tape(decoded,
                                    (size_t)tag.num_alphabet,
                                    tag_decoded,
                                    sizeof(tag_decoded));
    assert(tag_len == 1);
    assert(tag_decoded[0] == 1);

    free(cells);
    cyclic_tag_input_free(&cyclic);
    tag_system_free(&tag);
    printf("  compact_tag_to_rule110_round_trip: PASS\n");
}

int main(void) {
    printf("== test_tm_end_to_end ==\n");
    test_tm_to_tag_pipeline_surface();
    test_compact_tag_to_rule110_round_trip();
    printf("TM end-to-end: PASS\n");
    return 0;
}
