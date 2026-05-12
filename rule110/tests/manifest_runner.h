#ifndef MANIFEST_RUNNER_H
#define MANIFEST_RUNNER_H

#include <stddef.h>
#include <stdint.h>

/* Result of running one manifest assertion. */
typedef enum {
    MR_PASS = 0,
    MR_FAIL_HALT_REASON = 1,
    MR_FAIL_TAPE_MISMATCH = 2,
    MR_FAIL_LOAD = 3
} MrResult;

/* Run a cyclic-tag manifest file against an input bit-string, comparing the
   final tape to expected_tape after at most max_steps. Returns MR_PASS or a
   failure code. Prints details to stderr on failure. */
MrResult mr_run_ct_manifest(const char *manifest_path,
                            const char *input_bits,
                            const char *expected_final_tape,
                            size_t max_steps);

#endif
