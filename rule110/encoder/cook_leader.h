#ifndef COOK_LEADER_H
#define COOK_LEADER_H

#include <stddef.h>
#include <stdint.h>

extern const size_t COOK_LEADER_WIDTH;
extern const size_t COOK_LEADER_STABILITY_STEPS;

#define COOK_LEADER_PHASE_EXACT_OK 0
#define COOK_LEADER_PHASE_EXACT_CATALOG_MISSING 1

enum leader_kind {
    LEADER_REGULAR = 0,
    LEADER_SHORT = 1
};

enum leader_prepared_context {
    LEADER_PREPARED_AFTER_MOVING_DATA = 0,
    LEADER_PREPARED_AFTER_REJECTED_INVISIBLES = 1
};

typedef struct {
    int v[2];
    int w[2];
    int x[2];
    int y[6];
    size_t y_repeats;
    int total_mod4;
} CookLeaderPreparedPlacement;

void cook_leader_emit(uint8_t *out, size_t pos, size_t buf_len);
int cook_leader_prepared_k(enum leader_prepared_context context,
                           size_t c,
                           int *k_out);
int cook_leader_prepared_invisible_alignment(
    enum leader_prepared_context context,
    size_t c,
    int *alignment_out);
int cook_leader_prepared_placement(size_t c,
                                   CookLeaderPreparedPlacement *placement_out);
int cook_leader_emit_phase_exact(uint8_t *out, size_t pos, size_t buf_len);
int cook_leader_emit_phase_exact_kind(uint8_t *out,
                                      size_t pos,
                                      size_t buf_len,
                                      enum leader_kind kind);
int cook_leader_emit_phase_exact_kind_prepared(
    uint8_t *out,
    size_t pos,
    size_t buf_len,
    enum leader_kind kind,
    enum leader_prepared_context context,
    size_t c);
int cook_leader_emit_phase_exact_accept(uint8_t *out,
                                        size_t pos,
                                        size_t buf_len);
int cook_leader_emit_phase_exact_accept_kind(uint8_t *out,
                                             size_t pos,
                                             size_t buf_len,
                                             enum leader_kind kind);
int cook_leader_emit_phase_exact_accept_prepared(
    uint8_t *out,
    size_t pos,
    size_t buf_len,
    enum leader_kind kind,
    enum leader_prepared_context context,
    size_t c);
int cook_leader_emit_phase_exact_reject(uint8_t *out,
                                        size_t pos,
                                        size_t buf_len);
int cook_leader_emit_phase_exact_reject_kind(uint8_t *out,
                                             size_t pos,
                                             size_t buf_len,
                                             enum leader_kind kind);
int cook_leader_emit_phase_exact_reject_prepared(
    uint8_t *out,
    size_t pos,
    size_t buf_len,
    enum leader_kind kind,
    enum leader_prepared_context context,
    size_t c);

#endif
