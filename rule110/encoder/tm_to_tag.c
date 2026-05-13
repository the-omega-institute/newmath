#include "tm_to_tag.h"

#include <stdlib.h>
#include <string.h>

static int checked_mul_size(size_t a, size_t b, size_t *out) {
    if (out == NULL) return 0;
    if (a != 0 && b > ((size_t)-1) / a) return 0;
    *out = a * b;
    return 1;
}

static int checked_add_size(size_t a, size_t b, size_t *out) {
    if (out == NULL) return 0;
    if (a > ((size_t)-1) - b) return 0;
    *out = a + b;
    return 1;
}

static int pow_size(size_t base, size_t exp, size_t *out) {
    size_t acc = 1;

    if (out == NULL) return 0;
    for (size_t i = 0; i < exp; i++) {
        if (!checked_mul_size(acc, base, &acc)) return 0;
    }
    *out = acc;
    return 1;
}

static int valid_tm(const TMSpec *tm) {
    if (tm == NULL) return 0;
    if (tm->num_states <= 0 || tm->num_states > TM_TO_TAG_MAX_STATES) {
        return 0;
    }
    if (tm->num_symbols <= 0 || tm->num_symbols > TM_TO_TAG_MAX_SYMBOLS - 2) {
        return 0;
    }
    if (tm->halt_state < 0 || tm->halt_state >= tm->num_states) return 0;
    return 1;
}

static int symbol_index(const TMSpec *tm, int cls, int state, int tape_symbol) {
    int m = tm->num_states;
    int s = tm->num_symbols + 2;
    int base = 0;

    if (state < 0 || state >= m) return -1;
    if (cls < TM_TAG_CLASS_HS) {
        if (tape_symbol != 0) return -1;
        return (state * 4) + cls;
    }
    if (tape_symbol < 0 || tape_symbol >= s) return -1;
    base = 4 * m;
    return base + (((cls - TM_TAG_CLASS_HS) * m + state) * s) + tape_symbol;
}

static int append_repeat(uint8_t *buf,
                         size_t cap,
                         size_t *len,
                         int symbol,
                         size_t count) {
    if (buf == NULL || len == NULL || symbol < 0) return 0;
    if (count > cap || *len > cap - count) return 0;
    for (size_t i = 0; i < count; i++) {
        buf[*len] = (uint8_t)symbol;
        (*len)++;
    }
    return 1;
}

static char *copy_symbols(const uint8_t *symbols, size_t len) {
    char *out = (char *)malloc(len ? len : 1);

    if (out == NULL) return NULL;
    if (len > 0) memcpy(out, symbols, len);
    return out;
}

static int set_rule(TagSystem *tag,
                    int rule_index,
                    const uint8_t *rhs,
                    size_t rhs_len) {
    if (tag == NULL || rule_index < 0 || rule_index >= tag->num_rules) return 0;
    tag->rules[rule_index].appendant = copy_symbols(rhs, rhs_len);
    if (tag->rules[rule_index].appendant == NULL) return 0;
    tag->rules[rule_index].appendant_len = rhs_len;
    return 1;
}

static int transition_is_halt(const TMSpec *tm, int state, int tape_symbol) {
    const int move = tm->transitions[state][tape_symbol].move;
    const int next = tm->transitions[state][tape_symbol].next_state;

    return move == TM_MOVE_STAY || next == tm->halt_state;
}

static int build_base_rules(const TMSpec *tm, TagSystem *tag) {
    uint8_t rhs[TM_TO_TAG_MAX_RULES];
    int s = tm->num_symbols + 2;

    for (int i = 0; i < tm->num_states; i++) {
        size_t len = 0;

        for (int j = 0; j < s; j++) {
            if (!append_repeat(rhs,
                               sizeof(rhs),
                               &len,
                               symbol_index(tm, TM_TAG_CLASS_HS, i, j),
                               1)) {
                return 0;
            }
        }
        if (!set_rule(tag,
                      symbol_index(tm, TM_TAG_CLASS_H, i, 0),
                      rhs,
                      len)) {
            return 0;
        }

        len = 0;
        for (int j = 0; j < s; j++) {
            if (!append_repeat(rhs,
                               sizeof(rhs),
                               &len,
                               symbol_index(tm, TM_TAG_CLASS_LS, i, j),
                               1)) {
                return 0;
            }
        }
        if (!set_rule(tag,
                      symbol_index(tm, TM_TAG_CLASS_L, i, 0),
                      rhs,
                      len)) {
            return 0;
        }

        len = 0;
        for (int j = 0; j < s; j++) {
            if (!append_repeat(rhs,
                               sizeof(rhs),
                               &len,
                               symbol_index(tm, TM_TAG_CLASS_RS_PAIR, i, j),
                               1)) {
                return 0;
            }
        }
        if (!set_rule(tag,
                      symbol_index(tm, TM_TAG_CLASS_R, i, 0),
                      rhs,
                      len)) {
            return 0;
        }

        len = 0;
        if (!append_repeat(rhs,
                           sizeof(rhs),
                           &len,
                           symbol_index(tm, TM_TAG_CLASS_R, i, 0),
                           (size_t)s)) {
            return 0;
        }
        if (!set_rule(tag,
                      symbol_index(tm, TM_TAG_CLASS_RS, i, 0),
                      rhs,
                      len)) {
            return 0;
        }
    }
    return 1;
}

static int build_head_pair_rule(const TMSpec *tm,
                                TagSystem *tag,
                                int state,
                                int tape_symbol) {
    uint8_t rhs[TM_TO_TAG_MAX_RULES];
    size_t len = 0;
    int s = tm->num_symbols + 2;
    const int rule = symbol_index(tm,
                                  TM_TAG_CLASS_HS,
                                  state,
                                  tape_symbol);

    if (tape_symbol >= tm->num_symbols ||
        state == tm->halt_state ||
        transition_is_halt(tm, state, tape_symbol)) {
        return set_rule(tag, rule, rhs, 0);
    }

    {
        const int write = tm->transitions[state][tape_symbol].write_symbol;
        const int move = tm->transitions[state][tape_symbol].move;
        const int next = tm->transitions[state][tape_symbol].next_state;
        size_t first_count = 0;

        if (write < 0 || write >= tm->num_symbols) return 0;
        if (next < 0 || next >= tm->num_states) return 0;
        if (move == TM_MOVE_LEFT) {
            if (!checked_mul_size((size_t)s,
                                  (size_t)(s - (write + 1)),
                                  &first_count)) {
                return 0;
            }
            if (!append_repeat(rhs,
                               sizeof(rhs),
                               &len,
                               symbol_index(tm, TM_TAG_CLASS_RS, next, 0),
                               first_count)) {
                return 0;
            }
            if (!append_repeat(rhs,
                               sizeof(rhs),
                               &len,
                               symbol_index(tm, TM_TAG_CLASS_H, next, 0),
                               (size_t)(tape_symbol + 1))) {
                return 0;
            }
        } else if (move == TM_MOVE_RIGHT) {
            if (!append_repeat(rhs,
                               sizeof(rhs),
                               &len,
                               symbol_index(tm, TM_TAG_CLASS_H, next, 0),
                               (size_t)(tape_symbol + 1))) {
                return 0;
            }
            if (!checked_mul_size((size_t)s,
                                  (size_t)(s - (write + 1)),
                                  &first_count)) {
                return 0;
            }
            if (!append_repeat(rhs,
                               sizeof(rhs),
                               &len,
                               symbol_index(tm, TM_TAG_CLASS_L, next, 0),
                               first_count)) {
                return 0;
            }
        } else {
            return 0;
        }
    }
    return set_rule(tag, rule, rhs, len);
}

static int build_left_pair_rule(const TMSpec *tm,
                                TagSystem *tag,
                                int state,
                                int tape_symbol) {
    uint8_t rhs[TM_TO_TAG_MAX_RULES];
    size_t len = 0;
    int s = tm->num_symbols + 2;
    const int rule = symbol_index(tm,
                                  TM_TAG_CLASS_LS,
                                  state,
                                  tape_symbol);

    if (tape_symbol >= tm->num_symbols) {
        if (!append_repeat(rhs,
                           sizeof(rhs),
                           &len,
                           symbol_index(tm, TM_TAG_CLASS_L, state, 0),
                           (size_t)s)) {
            return 0;
        }
        return set_rule(tag, rule, rhs, len);
    }
    if (state == tm->halt_state || transition_is_halt(tm, state, tape_symbol)) {
        return set_rule(tag, rule, rhs, 0);
    }
    {
        const int move = tm->transitions[state][tape_symbol].move;
        const int next = tm->transitions[state][tape_symbol].next_state;

        if (next < 0 || next >= tm->num_states) return 0;
        if (move == TM_MOVE_LEFT) {
            if (!append_repeat(rhs,
                               sizeof(rhs),
                               &len,
                               symbol_index(tm, TM_TAG_CLASS_L, next, 0),
                               1)) {
                return 0;
            }
        } else if (move == TM_MOVE_RIGHT) {
            if (!append_repeat(rhs,
                               sizeof(rhs),
                               &len,
                               symbol_index(tm, TM_TAG_CLASS_L, next, 0),
                               (size_t)(s * s))) {
                return 0;
            }
        } else {
            return 0;
        }
    }
    return set_rule(tag, rule, rhs, len);
}

static int build_right_pair_rule(const TMSpec *tm,
                                 TagSystem *tag,
                                 int state,
                                 int tape_symbol) {
    uint8_t rhs[TM_TO_TAG_MAX_RULES];
    size_t len = 0;
    int s = tm->num_symbols + 2;
    const int rule = symbol_index(tm,
                                  TM_TAG_CLASS_RS_PAIR,
                                  state,
                                  tape_symbol);

    if (tape_symbol >= tm->num_symbols) {
        if (!append_repeat(rhs,
                           sizeof(rhs),
                           &len,
                           symbol_index(tm, TM_TAG_CLASS_R, state, 0),
                           (size_t)s)) {
            return 0;
        }
        return set_rule(tag, rule, rhs, len);
    }
    if (state == tm->halt_state || transition_is_halt(tm, state, tape_symbol)) {
        return set_rule(tag, rule, rhs, 0);
    }
    {
        const int move = tm->transitions[state][tape_symbol].move;
        const int next = tm->transitions[state][tape_symbol].next_state;

        if (next < 0 || next >= tm->num_states) return 0;
        if (move == TM_MOVE_LEFT) {
            if (!append_repeat(rhs,
                               sizeof(rhs),
                               &len,
                               symbol_index(tm, TM_TAG_CLASS_R, next, 0),
                               (size_t)(s * s))) {
                return 0;
            }
        } else if (move == TM_MOVE_RIGHT) {
            if (!append_repeat(rhs,
                               sizeof(rhs),
                               &len,
                               symbol_index(tm, TM_TAG_CLASS_R, next, 0),
                               1)) {
                return 0;
            }
        } else {
            return 0;
        }
    }
    return set_rule(tag, rule, rhs, len);
}

int tm_to_tag(const TMSpec *tm, TagSystem *out_tag) {
    int s = 0;

    if (!valid_tm(tm) || out_tag == NULL) return 0;
    memset(out_tag, 0, sizeof(*out_tag));
    s = tm->num_symbols + 2;
    out_tag->s_deletion = s;
    out_tag->num_alphabet = 4 * tm->num_states + 3 * tm->num_states * s;
    out_tag->num_rules = out_tag->num_alphabet;
    if (out_tag->num_rules > TM_TO_TAG_MAX_RULES) return 0;

    /*
       Cook 2009 §1.2, PDF page 2-3 lines 365-450 in Cork.tex:
       Phi has H/L/R/R* symbols per state and H/L/R state-symbol symbols;
       the tag-system rules below are the displayed Cocke-Minsky rules.
    */
    if (!build_base_rules(tm, out_tag)) goto fail;
    for (int state = 0; state < tm->num_states; state++) {
        for (int symbol = 0; symbol < s; symbol++) {
            if (!build_head_pair_rule(tm, out_tag, state, symbol)) goto fail;
            if (!build_left_pair_rule(tm, out_tag, state, symbol)) goto fail;
            if (!build_right_pair_rule(tm, out_tag, state, symbol)) goto fail;
        }
    }
    return 1;

fail:
    tag_system_free(out_tag);
    return 0;
}

int tm_to_tag_initial_tape(const TMSpec *tm,
                           const uint8_t *tm_tape,
                           size_t tm_tape_len,
                           int tm_initial_state,
                           uint8_t *out_tag_tape,
                           size_t *out_tag_tape_len) {
    size_t len = 0;
    size_t left_count = 0;
    size_t right_count = 0;
    int s = 0;

    if (!valid_tm(tm) ||
        tm_tape == NULL ||
        out_tag_tape == NULL ||
        out_tag_tape_len == NULL ||
        tm_initial_state < 0 ||
        tm_initial_state >= tm->num_states ||
        tm_tape_len == 0) {
        return 0;
    }

    /*
       Cook 2009 §1.2, PDF page 3 lines 450-456 in Cork.tex gives
       [H_state]^(1+s-c) [L_state]^(...) [R_state]^(...) for the
       finite central tape. This pilot uses blank periodic tails and
       places the head on the first supplied cell.
    */
    s = tm->num_symbols + 2;
    if (tm_tape[0] >= (uint8_t)tm->num_symbols) return 0;
    if (!append_repeat(out_tag_tape,
                       *out_tag_tape_len,
                       &len,
                       symbol_index(tm, TM_TAG_CLASS_H, tm_initial_state, 0),
                       (size_t)(s - (int)tm_tape[0]))) {
        return 0;
    }
    for (size_t k = 1; k < tm_tape_len; k++) {
        size_t pow = 0;
        size_t term = 0;

        if (tm_tape[k] >= (uint8_t)tm->num_symbols) return 0;
        if (!pow_size((size_t)s, k, &pow)) return 0;
        if (!checked_mul_size((size_t)(s - ((int)tm_tape[k] + 1)),
                              pow,
                              &term)) {
            return 0;
        }
        if (!checked_add_size(right_count, term, &right_count)) return 0;
    }
    if (!append_repeat(out_tag_tape,
                       *out_tag_tape_len,
                       &len,
                       symbol_index(tm, TM_TAG_CLASS_L, tm_initial_state, 0),
                       left_count)) {
        return 0;
    }
    if (!append_repeat(out_tag_tape,
                       *out_tag_tape_len,
                       &len,
                       symbol_index(tm, TM_TAG_CLASS_R, tm_initial_state, 0),
                       right_count)) {
        return 0;
    }
    *out_tag_tape_len = len;
    return 1;
}

void tag_system_free(TagSystem *tag) {
    if (tag == NULL) return;
    for (int i = 0; i < tag->num_rules && i < TM_TO_TAG_MAX_RULES; i++) {
        free(tag->rules[i].appendant);
        tag->rules[i].appendant = NULL;
        tag->rules[i].appendant_len = 0;
    }
    tag->num_alphabet = 0;
    tag->s_deletion = 0;
    tag->num_rules = 0;
}

int tm_tag_symbol_index(const TMSpec *tm,
                        int symbol_class,
                        int state,
                        int tape_symbol) {
    if (!valid_tm(tm)) return -1;
    return symbol_index(tm, symbol_class, state, tape_symbol);
}

int tag_to_tm_tape_inverse(const TMSpec *tm,
                           const uint8_t *tag_tape,
                           size_t tag_tape_len,
                           uint8_t *out_tm_tape,
                           size_t out_tm_tape_len,
                           int *out_state) {
    int s = 0;
    size_t pos = 0;
    int state = -1;
    size_t head_run = 0;
    size_t right_run = 0;

    if (!valid_tm(tm) ||
        tag_tape == NULL ||
        out_tm_tape == NULL ||
        out_state == NULL ||
        out_tm_tape_len == 0) {
        return 0;
    }
    memset(out_tm_tape, 0, out_tm_tape_len);
    s = tm->num_symbols + 2;

    for (int candidate = 0; candidate < tm->num_states; candidate++) {
        int h = symbol_index(tm, TM_TAG_CLASS_H, candidate, 0);

        head_run = 0;
        while (head_run < tag_tape_len && tag_tape[head_run] == (uint8_t)h) {
            head_run++;
        }
        if (head_run > 0 && head_run <= (size_t)s) {
            state = candidate;
            break;
        }
    }
    if (state < 0) return 0;
    {
        int head_symbol = s - (int)head_run;

        if (head_symbol < 0 || head_symbol >= tm->num_symbols) return 0;
        out_tm_tape[0] = (uint8_t)head_symbol;
    }

    pos = head_run;
    while (pos < tag_tape_len) {
        int r = symbol_index(tm, TM_TAG_CLASS_R, state, 0);

        if (tag_tape[pos] != (uint8_t)r) return 0;
        right_run++;
        pos++;
    }

    for (size_t cell = 1; cell < out_tm_tape_len; cell++) {
        size_t digit = right_run % (size_t)s;

        if (digit > (size_t)(s - 1)) return 0;
        if (digit < 2) {
            out_tm_tape[cell] = (uint8_t)((s - 1) - digit);
        } else {
            out_tm_tape[cell] = 0;
        }
        right_run /= (size_t)s;
    }
    *out_state = state;
    return 1;
}
