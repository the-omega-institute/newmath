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

static void free_event_result(GcDecResult *r) {
    free(r->event);
    r->event = NULL;
    r->event_len = 0;
}

static int decode_ext_step_holds(const char *input_bits) {
    uint8_t *in_bytes = NULL;
    size_t in_len = 0;
    if (!bits_to_bytes(input_bits, &in_bytes, &in_len)) return 0;

    GcBhistDecResult source = gc_bhist_decode(in_bytes, in_len, 8192);
    if (source.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&source);
        return 0;
    }

    size_t off = source.bytes_consumed;
    GcDecResult mark = gc_dec_event(in_bytes + off, in_len - off, 8192);
    if (mark.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&source);
        free_event_result(&mark);
        return 0;
    }

    off += mark.bytes_consumed;
    GcBhistDecResult result = gc_bhist_decode(in_bytes + off, in_len - off, 8192);
    if (result.status != GC_OK) {
        free(in_bytes);
        free_bhist_result(&source);
        free_event_result(&mark);
        free_bhist_result(&result);
        return 0;
    }

    int exact_three = (off + result.bytes_consumed == in_len);
    int mark_is_bit = (mark.event_len == 1) && (mark.event[0] == 0 || mark.event[0] == 1);
    int depth_ok = (result.bhist.depth == source.bhist.depth + 1);
    int head_ok = mark_is_bit && depth_ok && result.bhist.choices[0] == mark.event[0];
    int tail_ok = depth_ok &&
                  (source.bhist.depth == 0 ||
                   memcmp(result.bhist.choices + 1,
                          source.bhist.choices,
                          source.bhist.depth) == 0);
    int holds = exact_three && mark_is_bit && depth_ok && head_ok && tail_ok;

    free(in_bytes);
    free_bhist_result(&source);
    free_event_result(&mark);
    free_bhist_result(&result);
    return holds;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void test_ext_step_enum(void) {
    assert(decode_ext_step_holds("11011011"));
    assert(decode_ext_step_holds("1110111011"));
    assert(decode_ext_step_holds("0110110011"));
    assert(decode_ext_step_holds("10111011101011"));
    assert(decode_ext_step_holds("01011011001011"));
    assert(!decode_ext_step_holds("1101111"));
    assert(!decode_ext_step_holds("01101110011"));
    assert(!decode_ext_step_holds("1011101101011"));
    assert_manifest_smoke("manifests/ext/ext_step.enum.ct", "11011011");
    printf("  ext_step.enum: 8/8 cases PASS\n");
}

static void test_ext_step_algo(void) {
    assert(decode_ext_step_holds("11011011"));
    assert(decode_ext_step_holds("1110111011"));
    assert(decode_ext_step_holds("0110110011"));
    assert(decode_ext_step_holds("10111011101011"));
    assert(decode_ext_step_holds("01011011001011"));
    assert(!decode_ext_step_holds("1101111"));
    assert(!decode_ext_step_holds("01101110011"));
    assert(!decode_ext_step_holds("1011101101011"));
    assert_manifest_smoke("manifests/ext/ext_step.algo.ct", "11011011");
    printf("  ext_step.algo: 8/8 cases PASS\n");
}

int main(void) {
    printf("== test_ext ==\n");
    test_ext_step_enum();
    test_ext_step_algo();
    printf("ALL test_ext assertions passed (16 Ext step cases + 2-manifest pipeline smoke)\n");
    return 0;
}
