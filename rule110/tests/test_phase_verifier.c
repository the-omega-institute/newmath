#include "phase_verifier.h"

#include <assert.h>
#include <stdio.h>

static void test_required_verified_entries(void) {
    assert(phase_verifier_check("A", NULL, 1) == PHV_OK);
    assert(phase_verifier_check("C2", "A", 1) == PHV_OK);
    assert(phase_verifier_check("Ebar", "A", 1) == PHV_OK);

    printf("  required_verified_entries: PASS\n");
}

static void test_result_codes(void) {
    assert(phase_verifier_check("D", "A", 1) == PHV_NOT_REGISTERED);
    assert(phase_verifier_check("Gun", "A", 1) == PHV_NO_METADATA);
    assert(phase_verifier_check("F", "A", 1) == PHV_NOT_PHASE_EXACT);

    printf("  result_codes: PASS\n");
}

int main(void) {
    printf("== test_phase_verifier ==\n");
    test_required_verified_entries();
    test_result_codes();
    printf("ALL test_phase_verifier tests passed\n");
    return 0;
}
