#ifndef PHASE_VERIFIER_H
#define PHASE_VERIFIER_H

#include <stddef.h>
#include <stdint.h>

enum PhaseVerifyResult {
    PHV_OK = 0,
    PHV_NOT_REGISTERED = 1,
    PHV_NOT_PHASE_EXACT = 2,
    PHV_NO_METADATA = 3
};

int phase_verifier_check(const char *glider_name,
                         const char *neighbor,
                         int phase);

#endif
