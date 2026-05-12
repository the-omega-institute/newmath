#include "cook_leader.h"
#include <string.h>

const size_t COOK_LEADER_WIDTH = 20;
const size_t COOK_LEADER_STABILITY_STEPS = 500;

void cook_leader_emit(uint8_t *out, size_t pos, size_t buf_len) {
    static const uint8_t LEADER_ROW0[20] =
        {1, 0, 1, 1, 1, 1, 1, 1, 0, 1,
         0, 1, 0, 0, 0, 0, 1, 1, 0, 0};

    /*
       Best-effort Cook leader seed for the phase-B behavioral encoder.
       The row-0 overwrite is "10111111010100001100" on a pre-filled
       Cook ether background. It was selected by direct local Rule 110
       simulation because it leaves a detectable localized disturbance
       after 500 steps while preserving far-field ether in the tested
       light-cone guards. This is not a phase-exact transcription of
       Cook 2004 section 5.
    */
    if (pos > buf_len || COOK_LEADER_WIDTH > buf_len - pos) return;

    memcpy(out + pos, LEADER_ROW0, sizeof(LEADER_ROW0));
}

int cook_leader_emit_phase_exact(uint8_t *out, size_t pos, size_t buf_len) {
#if defined(COOK_PHASE_EXACT_BH_AVAILABLE)
    /*
       TODO(L3.1 B-H): replace this sentinel with the Cook leader packet once
       the B/C/D/E/F/H phase catalog includes verified masks, ether phase,
       and legal spacings. The leader is a clock/synchronizer package, not the
       20-cell behavioral marker above; it must place its A-bearing head and
       B-H support particles so that the first ossifier interaction restores
       the cyclic-tag production phase.
    */
#endif
    (void)out;
    (void)pos;
    (void)buf_len;
    return COOK_LEADER_PHASE_EXACT_CATALOG_MISSING;
}
