#include "manifest_runner.h"
#include <assert.h>
#include <stdio.h>

static void test_synthetic_ether_manifest(void) {
    MrResult r = mr_run_r110_manifest(
        "manifests/test_fixtures/synthetic.r110",
        0);

    assert(r == MR_PASS);
    printf("  synthetic_ether_manifest: PASS\n");
}

int main(void) {
    printf("== test_manifest_runner_r110 ==\n");
    test_synthetic_ether_manifest();
    printf("ALL test_manifest_runner_r110 tests passed\n");
    return 0;
}
