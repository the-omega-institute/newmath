#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

static int bits_to_bytes(const char *input_bits, uint8_t **out, size_t *out_len) {
    size_t in_len = strlen(input_bits);
    uint8_t *in_bytes = (uint8_t *)malloc(in_len ? in_len : 1);
    if (in_bytes == NULL) return 0;
    for (size_t i = 0; i < in_len; i++) {
        if (input_bits[i] != '0' && input_bits[i] != '1') {
            free(in_bytes);
            return 0;
        }
        in_bytes[i] = (uint8_t)(input_bits[i] - '0');
    }
    *out = in_bytes;
    *out_len = in_len;
    return 1;
}

static void free_bhist_result(GcBhistDecResult *r) {
    free(r->bhist.choices);
    r->bhist.choices = NULL;
    r->bhist.depth = 0;
}

static int decode_cont_holds(const char *input_bits) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult h = gc_bhist_decode(in_bytes, in_len, 8192);
    if (h.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&h);
        return 0;
    }

    size_t off = h.bytes_consumed;
    GcBhistDecResult k = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (k.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&h);
        free_bhist_result(&k);
        return 0;
    }

    off += k.bytes_consumed;
    GcBhistDecResult r = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (r.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&h);
        free_bhist_result(&k);
        free_bhist_result(&r);
        return 0;
    }

    int exact_three = (off + r.bytes_consumed == in_len);
    int depth_ok = (r.bhist.depth == h.bhist.depth + k.bhist.depth);
    int prefix_ok = (k.bhist.depth == 0 ||
                     memcmp(r.bhist.choices,
                            k.bhist.choices,
                            k.bhist.depth) == 0);
    int suffix_ok = (h.bhist.depth == 0 ||
                     memcmp(r.bhist.choices + k.bhist.depth,
                            h.bhist.choices,
                            h.bhist.depth) == 0);
    int holds = exact_three && depth_ok && prefix_ok && suffix_ok;

    free(in_bytes);
    free_bhist_result(&h);
    free_bhist_result(&k);
    free_bhist_result(&r);
    return holds;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void assert_cont_basic_cases(void) {
    assert(decode_cont_holds("111111"));
    assert(decode_cont_holds("01111011"));
    assert(decode_cont_holds("1110111011"));
    assert(decode_cont_holds("011101110011"));
    assert(decode_cont_holds("1011010110101011"));
    assert(decode_cont_holds("010111001110001011"));
    assert(!decode_cont_holds("1111011"));
    assert(!decode_cont_holds("1101111"));
    assert(!decode_cont_holds("011101101011"));
    assert(!decode_cont_holds("101101110011"));
}

static void test_cont_basic_enum(void) {
    assert_cont_basic_cases();
    assert_manifest_smoke("manifests/cont/cont_basic.enum.ct", "111111");
    printf("  cont_basic.enum: 10/10 cases PASS\n");
}

static void test_cont_basic_algo(void) {
    assert_cont_basic_cases();
    assert_manifest_smoke("manifests/cont/cont_basic.algo.ct", "111111");
    printf("  cont_basic.algo: 10/10 cases PASS\n");
}

int main(void) {
    printf("== test_cont ==\n");
    test_cont_basic_enum();
    test_cont_basic_algo();
    printf("ALL test_cont assertions passed (20 Cont cases + 2-manifest pipeline smoke)\n");
    return 0;
}
