#ifndef TM_TO_TAG_H
#define TM_TO_TAG_H

#include <stddef.h>
#include <stdint.h>

#define TM_TO_TAG_MAX_STATES 16
#define TM_TO_TAG_MAX_SYMBOLS 16
#define TM_TO_TAG_MAX_RULES 1024

#define TM_MOVE_LEFT  (-1)
#define TM_MOVE_STAY  0
#define TM_MOVE_RIGHT 1

#define TM_TAG_CLASS_H 0
#define TM_TAG_CLASS_L 1
#define TM_TAG_CLASS_R 2
#define TM_TAG_CLASS_RS 3
#define TM_TAG_CLASS_HS 4
#define TM_TAG_CLASS_LS 5
#define TM_TAG_CLASS_RS_PAIR 6

typedef struct {
    int num_states;
    int num_symbols;
    struct {
        int write_symbol;
        int move;
        int next_state;
    } transitions[TM_TO_TAG_MAX_STATES][TM_TO_TAG_MAX_SYMBOLS];
    int halt_state;
} TMSpec;

typedef struct {
    int num_alphabet;
    int s_deletion;
    int num_rules;
    struct {
        char *appendant;
        size_t appendant_len;
    } rules[TM_TO_TAG_MAX_RULES];
} TagSystem;

int tm_to_tag(const TMSpec *tm, TagSystem *out_tag);

int tm_to_tag_initial_tape(const TMSpec *tm,
                           const uint8_t *tm_tape,
                           size_t tm_tape_len,
                           int tm_initial_state,
                           uint8_t *out_tag_tape,
                           size_t *out_tag_tape_len);

void tag_system_free(TagSystem *tag);

int tm_tag_symbol_index(const TMSpec *tm,
                        int symbol_class,
                        int state,
                        int tape_symbol);

int tag_to_tm_tape_inverse(const TMSpec *tm,
                           const uint8_t *tag_tape,
                           size_t tag_tape_len,
                           uint8_t *out_tm_tape,
                           size_t out_tm_tape_len,
                           int *out_state);

#endif
