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
