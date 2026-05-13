#include "tag_to_cyclic.h"

#include <stdlib.h>
#include <string.h>

static int checked_mul_size(size_t a, size_t b, size_t *out) {
    if (out == NULL) return 0;
    if (a != 0 && b > ((size_t)-1) / a) return 0;
    *out = a * b;
    return 1;
}

static int append_unary_symbol(uint8_t *out,
                               size_t cap,
                               size_t *len,
                               size_t alphabet,
                               size_t symbol) {
    if (out == NULL || len == NULL || alphabet == 0 || symbol >= alphabet) {
        return 0;
    }
    if (*len > cap || alphabet > cap - *len) return 0;
    for (size_t i = 0; i < alphabet; i++) {
        out[*len + i] = (uint8_t)(i == symbol ? 1 : 0);
    }
    *len += alphabet;
    return 1;
}

static int encode_symbol_string(const uint8_t *symbols,
                                size_t symbol_len,
                                size_t alphabet,
                                uint8_t **out_bits,
                                size_t *out_len) {
    size_t cap = 0;
    size_t len = 0;
    uint8_t *bits = NULL;

    if (out_bits == NULL || out_len == NULL || alphabet == 0) return 0;
    *out_bits = NULL;
    *out_len = 0;
    if (!checked_mul_size(symbol_len, alphabet, &cap)) return 0;
    bits = (uint8_t *)malloc(cap ? cap : 1);
    if (bits == NULL) return 0;
    for (size_t i = 0; i < symbol_len; i++) {
        if (symbols[i] >= alphabet ||
            !append_unary_symbol(bits,
                                 cap,
                                 &len,
                                 alphabet,
                                 symbols[i])) {
            free(bits);
            return 0;
        }
    }
    *out_bits = bits;
    *out_len = len;
    return 1;
}

int tag_to_cyclic(const TagSystem *tag,
                  const uint8_t *tag_tape,
                  size_t tag_tape_len,
                  CyclicTagInput *out_cyclic) {
    size_t alphabet = 0;
    size_t production_count = 0;

    if (tag == NULL ||
        out_cyclic == NULL ||
        tag->num_alphabet <= 0 ||
        tag->s_deletion <= 0 ||
        tag->num_rules <= 0 ||
        tag->num_rules != tag->num_alphabet ||
        (tag_tape_len > 0 && tag_tape == NULL)) {
        return 0;
    }
    memset(out_cyclic, 0, sizeof(*out_cyclic));
    alphabet = (size_t)tag->num_alphabet;
    if (!checked_mul_size((size_t)tag->s_deletion,
                          alphabet,
                          &production_count)) {
        return 0;
    }

    /*
       Cook 2009 §1.3, PDF page 3 lines 482-528 in Cork.tex:
       phi_i maps to N^(i-1) Y N^(|Phi|-i); the cyclic appendant list
       is the ordered tag-rule list followed by empty appendants to
       length s|Phi|.
    */
    out_cyclic->productions =
        (uint8_t **)calloc(production_count, sizeof(uint8_t *));
    out_cyclic->prod_lens =
        (size_t *)calloc(production_count, sizeof(size_t));
    if (out_cyclic->productions == NULL || out_cyclic->prod_lens == NULL) {
        cyclic_tag_input_free(out_cyclic);
        return 0;
    }
    out_cyclic->num_productions = production_count;
    for (size_t i = 0; i < alphabet; i++) {
        const uint8_t *rhs = (const uint8_t *)tag->rules[i].appendant;
        size_t rhs_len = tag->rules[i].appendant_len;

        if (rhs_len > 0 && rhs == NULL) {
            cyclic_tag_input_free(out_cyclic);
            return 0;
        }
        if (!encode_symbol_string(rhs,
                                  rhs_len,
                                  alphabet,
                                  &out_cyclic->productions[i],
                                  &out_cyclic->prod_lens[i])) {
            cyclic_tag_input_free(out_cyclic);
            return 0;
        }
    }
    if (!encode_symbol_string(tag_tape,
                              tag_tape_len,
                              alphabet,
                              &out_cyclic->initial_tape,
                              &out_cyclic->tape_len)) {
        cyclic_tag_input_free(out_cyclic);
        return 0;
    }
    return 1;
}

void cyclic_tag_input_free(CyclicTagInput *cyclic) {
    if (cyclic == NULL) return;
    if (cyclic->productions != NULL) {
        for (size_t i = 0; i < cyclic->num_productions; i++) {
            free(cyclic->productions[i]);
            cyclic->productions[i] = NULL;
        }
    }
    free(cyclic->productions);
    free(cyclic->prod_lens);
    free(cyclic->initial_tape);
    cyclic->productions = NULL;
    cyclic->prod_lens = NULL;
    cyclic->initial_tape = NULL;
    cyclic->num_productions = 0;
    cyclic->tape_len = 0;
}
