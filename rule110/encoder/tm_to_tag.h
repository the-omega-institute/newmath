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

#endif
