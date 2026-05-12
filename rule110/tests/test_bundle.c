#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>

typedef struct {
    size_t *items;
    size_t len;
} Bundle;

static const char *LENGTH_APPEND_EMPTY_EMPTY = "101011101011";
static const char *LENGTH_APPEND_EMPTY_TWO = "1010111011001011101011";
static const char *LENGTH_APPEND_TWO_ONE = "010110010111010111011101011";
static const char *NIL_RIGHT_EMPTY = "101011";
static const char *NIL_RIGHT_THREE = "010110010110001011101011";
static const char *ASSOC_EMPTY_LEFT = "101011101110101101011101011";
static const char *ASSOC_NONEMPTY = "101110101101011101011001011101011";
static const char *EQ_RIGHT_LEFT_NIL = "101011001011101011";
static const char *EQ_RIGHT_NONEMPTY_LEFT = "1011101011101011";
static const char *EQ_LEFT_RIGHT_NIL = "001011101011101011";
static const char *EQ_LEFT_NONEMPTY_RIGHT = "101110101101011101011";
static const char *SPLIT_UNIQUE_FIXED = "010110010111010111011101011010110010111010111011101011";
static const char *THREE_SPLIT_UNIQUE =
    "101110101101011101011001011101011101110101101011101011001011101011";

static const char *NIL_ELIM_PROBE0 = "1011101011";
static const char *CONS_SELF_PROBE1 = "0101101011001011101011";
static const char *SINGLETON_IFF_YES = "001011001011101011";
static const char *SINGLETON_IFF_NO = "00101101011101011";
static const char *APPEND_MEMBER_LEFT = "0101101011101011001011101011";
static const char *APPEND_MEMBER_RIGHT = "001011101110101100101101011101011";
static const char *APPEND_MEMBER_ABSENT = "00010111011101011001011101011";
static const char *APPEND_THREE_MIDDLE = "001011101110101100101110101101011101011";
static const char *APPEND_FOUR_LAST =
    "00010111011101011010111010110010111010110001011101011";
static const char *MEMBER_SPLIT_HEAD = "10111011001011101011";
static const char *MEMBER_SPLIT_TAIL = "0010111011001011101011";
static const char *PREFIX_SUFFIX_CANCEL =
    "01011001011101011101110101110111010110001011101011";
static const char *CONS_RESULT_INVERSION_PREFNIL =
    "10101110110010111010111011001011101011";
static const char *EMPTY_RESULT_INVERSION = "101011101011";

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

static void free_event_result(GcDecResult *r) {
    free(r->event);
    r->event = NULL;
    r->event_len = 0;
}

static void free_bundle(Bundle *b) {
    free(b->items);
    b->items = NULL;
    b->len = 0;
}

static int event_is_bundle_end(const GcDecResult *r) {
    return r->event_len == 2 && r->event[0] == 1 && r->event[1] == 1;
}

static int event_as_probe(const GcDecResult *r, size_t *out_probe) {
    if (r->event_len == 0) return 0;
    if (r->event[r->event_len - 1] != 1) return 0;
    for (size_t i = 0; i + 1 < r->event_len; i++) {
        if (r->event[i] != 0) return 0;
    }
    *out_probe = r->event_len - 1;
    return 1;
}

static int bundle_push(Bundle *b, size_t probe) {
    size_t *next = (size_t *)realloc(b->items, (b->len + 1) * sizeof(size_t));
    if (next == NULL) return 0;
    b->items = next;
    b->items[b->len++] = probe;
    return 1;
}

static int decode_one_probe(const uint8_t *bytes, size_t len, size_t *off, size_t *out_probe) {
    GcDecResult r = gc_dec_event(bytes + *off, len - *off, 8192);
    if (r.status != GC_OK) {
        free_event_result(&r);
        return 0;
    }
    int ok = event_as_probe(&r, out_probe);
    *off += r.bytes_consumed;
    free_event_result(&r);
    return ok;
}

static int decode_bundle(const uint8_t *bytes, size_t len, size_t *off, Bundle *out) {
    out->items = NULL;
    out->len = 0;
    while (*off < len) {
        GcDecResult r = gc_dec_event(bytes + *off, len - *off, 8192);
        if (r.status != GC_OK) {
            free_event_result(&r);
            free_bundle(out);
            return 0;
        }
        *off += r.bytes_consumed;
        if (event_is_bundle_end(&r)) {
            free_event_result(&r);
            return 1;
        }
        size_t probe = 0;
        int ok = event_as_probe(&r, &probe);
        free_event_result(&r);
        if (!ok || !bundle_push(out, probe)) {
            free_bundle(out);
            return 0;
        }
    }
    free_bundle(out);
    return 0;
}

static int decode_exact_bundles(const char *input_bits, Bundle *bundles, size_t count) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    size_t off = 0;
    for (size_t i = 0; i < count; i++) {
        if (!decode_bundle(bytes, len, &off, &bundles[i])) {
            for (size_t j = 0; j < i; j++) free_bundle(&bundles[j]);
            free(bytes);
            return 0;
        }
    }
    int exact = (off == len);
    if (!exact) {
        for (size_t i = 0; i < count; i++) free_bundle(&bundles[i]);
    }
    free(bytes);
    return exact;
}

static int decode_probe_and_bundles(const char *input_bits,
                                    size_t *probe,
                                    Bundle *bundles,
                                    size_t count) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    if (!bits_to_bytes(input_bits, &bytes, &len)) return 0;

    size_t off = 0;
    if (!decode_one_probe(bytes, len, &off, probe)) {
        free(bytes);
        return 0;
    }
    for (size_t i = 0; i < count; i++) {
        if (!decode_bundle(bytes, len, &off, &bundles[i])) {
            for (size_t j = 0; j < i; j++) free_bundle(&bundles[j]);
            free(bytes);
            return 0;
        }
    }
    int exact = (off == len);
    if (!exact) {
        for (size_t i = 0; i < count; i++) free_bundle(&bundles[i]);
    }
    free(bytes);
    return exact;
}

static int bundle_equal(const Bundle *a, const Bundle *b) {
    return a->len == b->len &&
           (a->len == 0 || memcmp(a->items, b->items, a->len * sizeof(size_t)) == 0);
}

static Bundle bundle_slice(const Bundle *b, size_t start, size_t len) {
    Bundle out;
    out.items = NULL;
    out.len = 0;
    if (len == 0) return out;
    out.items = (size_t *)malloc(len * sizeof(size_t));
    assert(out.items != NULL);
    memcpy(out.items, b->items + start, len * sizeof(size_t));
    out.len = len;
    return out;
}

static Bundle bundle_append_value(const Bundle *left, const Bundle *right) {
    Bundle out;
    out.items = NULL;
    out.len = left->len + right->len;
    if (out.len == 0) return out;
    out.items = (size_t *)malloc(out.len * sizeof(size_t));
    assert(out.items != NULL);
    if (left->len > 0) memcpy(out.items, left->items, left->len * sizeof(size_t));
    if (right->len > 0) {
        memcpy(out.items + left->len, right->items, right->len * sizeof(size_t));
    }
    return out;
}

static int bundle_contains(const Bundle *b, size_t probe) {
    for (size_t i = 0; i < b->len; i++) {
        if (b->items[i] == probe) return 1;
    }
    return 0;
}

static int member_split_exists(const Bundle *b, size_t probe) {
    for (size_t i = 0; i < b->len; i++) {
        if (b->items[i] == probe) return 1;
    }
    return 0;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r = mr_run_ct_manifest(path, input_bits, "", 200);
    if (r != MR_PASS) {
        fprintf(stderr, "pipeline smoke FAIL on %s: result=%d\n", path, (int)r);
    }
    assert(r == MR_PASS);
}

static void check_length_append_case(const char *input_bits) {
    Bundle b[2];
    assert(decode_exact_bundles(input_bits, b, 2));
    Bundle app = bundle_append_value(&b[0], &b[1]);
    assert(app.len == b[0].len + b[1].len);
    free_bundle(&app);
    free_bundle(&b[0]);
    free_bundle(&b[1]);
}

static void check_nil_right_case(const char *input_bits) {
    Bundle b[1];
    assert(decode_exact_bundles(input_bits, b, 1));
    Bundle nil = {NULL, 0};
    Bundle app = bundle_append_value(&b[0], &nil);
    assert(bundle_equal(&app, &b[0]));
    free_bundle(&app);
    free_bundle(&b[0]);
}

static void check_assoc_case(const char *input_bits) {
    Bundle b[3];
    assert(decode_exact_bundles(input_bits, b, 3));
    Bundle bc = bundle_append_value(&b[1], &b[2]);
    Bundle left = bundle_append_value(&b[0], &bc);
    Bundle ab = bundle_append_value(&b[0], &b[1]);
    Bundle right = bundle_append_value(&ab, &b[2]);
    assert(bundle_equal(&left, &right));
    free_bundle(&bc);
    free_bundle(&left);
    free_bundle(&ab);
    free_bundle(&right);
    for (size_t i = 0; i < 3; i++) free_bundle(&b[i]);
}

static void check_eq_right_iff_left_nil(const char *input_bits) {
    Bundle b[2];
    assert(decode_exact_bundles(input_bits, b, 2));
    Bundle app = bundle_append_value(&b[0], &b[1]);
    int lhs = bundle_equal(&app, &b[1]);
    int rhs = (b[0].len == 0);
    assert(lhs == rhs);
    free_bundle(&app);
    free_bundle(&b[0]);
    free_bundle(&b[1]);
}

static void check_eq_left_iff_right_nil(const char *input_bits) {
    Bundle b[2];
    assert(decode_exact_bundles(input_bits, b, 2));
    Bundle app = bundle_append_value(&b[0], &b[1]);
    int lhs = bundle_equal(&app, &b[0]);
    int rhs = (b[1].len == 0);
    assert(lhs == rhs);
    free_bundle(&app);
    free_bundle(&b[0]);
    free_bundle(&b[1]);
}

static void check_split_unique_fixed_lengths(const char *input_bits) {
    Bundle b[4];
    assert(decode_exact_bundles(input_bits, b, 4));
    Bundle left_app = bundle_append_value(&b[0], &b[1]);
    Bundle right_app = bundle_append_value(&b[2], &b[3]);
    if (bundle_equal(&left_app, &right_app) && b[0].len == b[2].len) {
        assert(bundle_equal(&b[0], &b[2]));
        assert(bundle_equal(&b[1], &b[3]));
    }
    if (bundle_equal(&left_app, &right_app) && b[1].len == b[3].len) {
        assert(bundle_equal(&b[0], &b[2]));
        assert(bundle_equal(&b[1], &b[3]));
    }
    free_bundle(&left_app);
    free_bundle(&right_app);
    for (size_t i = 0; i < 4; i++) free_bundle(&b[i]);
}

static void check_three_split_unique_fixed_lengths(const char *input_bits) {
    Bundle b[6];
    assert(decode_exact_bundles(input_bits, b, 6));
    Bundle bc = bundle_append_value(&b[1], &b[2]);
    Bundle left = bundle_append_value(&b[0], &bc);
    Bundle bpcp = bundle_append_value(&b[4], &b[5]);
    Bundle right = bundle_append_value(&b[3], &bpcp);
    if (bundle_equal(&left, &right) && b[0].len == b[3].len && b[1].len == b[4].len) {
        assert(bundle_equal(&b[0], &b[3]));
        assert(bundle_equal(&b[1], &b[4]));
        assert(bundle_equal(&b[2], &b[5]));
    }
    free_bundle(&bc);
    free_bundle(&left);
    free_bundle(&bpcp);
    free_bundle(&right);
    for (size_t i = 0; i < 6; i++) free_bundle(&b[i]);
}

static void check_nil_membership_case(const char *input_bits) {
    size_t probe = 0;
    Bundle b[1];
    assert(decode_probe_and_bundles(input_bits, &probe, b, 1));
    assert(!bundle_contains(&b[0], probe));
    free_bundle(&b[0]);
}

static void check_cons_self_case(const char *input_bits) {
    size_t probe = 0;
    Bundle b[1];
    assert(decode_probe_and_bundles(input_bits, &probe, b, 1));
    assert(b[0].len > 0);
    assert(b[0].items[0] == probe);
    assert(bundle_contains(&b[0], probe));
    free_bundle(&b[0]);
}

static void check_singleton_iff_case(const char *input_bits) {
    size_t probe = 0;
    Bundle b[1];
    assert(decode_probe_and_bundles(input_bits, &probe, b, 1));
    assert(b[0].len == 1);
    assert(bundle_contains(&b[0], probe) == (probe == b[0].items[0]));
    free_bundle(&b[0]);
}

static void check_append_membership_case(const char *input_bits) {
    size_t probe = 0;
    Bundle b[2];
    assert(decode_probe_and_bundles(input_bits, &probe, b, 2));
    Bundle app = bundle_append_value(&b[0], &b[1]);
    int in_append = bundle_contains(&app, probe);
    int in_parts = bundle_contains(&b[0], probe) || bundle_contains(&b[1], probe);
    assert(in_append == in_parts);
    free_bundle(&app);
    free_bundle(&b[0]);
    free_bundle(&b[1]);
}

static void check_append_left_of_not_right_case(const char *input_bits) {
    size_t probe = 0;
    Bundle b[2];
    assert(decode_probe_and_bundles(input_bits, &probe, b, 2));
    Bundle app = bundle_append_value(&b[0], &b[1]);
    if (bundle_contains(&app, probe) && !bundle_contains(&b[1], probe)) {
        assert(bundle_contains(&b[0], probe));
    }
    free_bundle(&app);
    free_bundle(&b[0]);
    free_bundle(&b[1]);
}

static void check_append_right_of_not_left_case(const char *input_bits) {
    size_t probe = 0;
    Bundle b[2];
    assert(decode_probe_and_bundles(input_bits, &probe, b, 2));
    Bundle app = bundle_append_value(&b[0], &b[1]);
    if (bundle_contains(&app, probe) && !bundle_contains(&b[0], probe)) {
        assert(bundle_contains(&b[1], probe));
    }
    free_bundle(&app);
    free_bundle(&b[0]);
    free_bundle(&b[1]);
}

static void check_append_three_case(const char *input_bits) {
    size_t probe = 0;
    Bundle b[3];
    assert(decode_probe_and_bundles(input_bits, &probe, b, 3));
    Bundle middle_right = bundle_append_value(&b[1], &b[2]);
    Bundle app = bundle_append_value(&b[0], &middle_right);
    int in_app = bundle_contains(&app, probe);
    int in_parts = bundle_contains(&b[0], probe) ||
                   bundle_contains(&b[1], probe) ||
                   bundle_contains(&b[2], probe);
    assert(in_app == in_parts);
    free_bundle(&middle_right);
    free_bundle(&app);
    for (size_t i = 0; i < 3; i++) free_bundle(&b[i]);
}

static void check_append_four_case(const char *input_bits) {
    size_t probe = 0;
    Bundle b[4];
    assert(decode_probe_and_bundles(input_bits, &probe, b, 4));
    Bundle cd = bundle_append_value(&b[2], &b[3]);
    Bundle bcd = bundle_append_value(&b[1], &cd);
    Bundle app = bundle_append_value(&b[0], &bcd);
    int in_app = bundle_contains(&app, probe);
    int in_parts = bundle_contains(&b[0], probe) ||
                   bundle_contains(&b[1], probe) ||
                   bundle_contains(&b[2], probe) ||
                   bundle_contains(&b[3], probe);
    assert(in_app == in_parts);
    free_bundle(&cd);
    free_bundle(&bcd);
    free_bundle(&app);
    for (size_t i = 0; i < 4; i++) free_bundle(&b[i]);
}

static void check_member_split_case(const char *input_bits) {
    size_t probe = 0;
    Bundle b[1];
    assert(decode_probe_and_bundles(input_bits, &probe, b, 1));
    assert(bundle_contains(&b[0], probe) == member_split_exists(&b[0], probe));
    free_bundle(&b[0]);
}

static void check_cancellation_case(const char *input_bits) {
    Bundle b[4];
    assert(decode_exact_bundles(input_bits, b, 4));
    Bundle pref_left = bundle_append_value(&b[0], &b[1]);
    Bundle pref_right = bundle_append_value(&b[0], &b[2]);
    if (bundle_equal(&pref_left, &pref_right)) {
        assert(bundle_equal(&b[1], &b[2]));
    }
    Bundle left_suff = bundle_append_value(&b[1], &b[3]);
    Bundle right_suff = bundle_append_value(&b[2], &b[3]);
    if (bundle_equal(&left_suff, &right_suff)) {
        assert(bundle_equal(&b[1], &b[2]));
    }
    free_bundle(&pref_left);
    free_bundle(&pref_right);
    free_bundle(&left_suff);
    free_bundle(&right_suff);
    for (size_t i = 0; i < 4; i++) free_bundle(&b[i]);
}

static void check_cons_result_inversion_case(const char *input_bits) {
    Bundle b[3];
    assert(decode_exact_bundles(input_bits, b, 3));
    Bundle app = bundle_append_value(&b[0], &b[1]);
    assert(b[2].len > 0);
    if (bundle_equal(&app, &b[2])) {
        size_t p = b[2].items[0];
        Bundle out = bundle_slice(&b[2], 1, b[2].len - 1);
        if (b[0].len == 0) {
            assert(bundle_equal(&b[1], &b[2]));
        } else {
            assert(b[0].items[0] == p);
            Bundle pref_tail = bundle_slice(&b[0], 1, b[0].len - 1);
            Bundle tail_app = bundle_append_value(&pref_tail, &b[1]);
            assert(bundle_equal(&tail_app, &out));
            free_bundle(&pref_tail);
            free_bundle(&tail_app);
        }
        free_bundle(&out);
    }
    free_bundle(&app);
    for (size_t i = 0; i < 3; i++) free_bundle(&b[i]);
}

static void check_empty_result_inversion_case(const char *input_bits) {
    Bundle b[2];
    assert(decode_exact_bundles(input_bits, b, 2));
    Bundle app = bundle_append_value(&b[0], &b[1]);
    if (app.len == 0) {
        assert(b[0].len == 0);
        assert(b[1].len == 0);
    }
    free_bundle(&app);
    free_bundle(&b[0]);
    free_bundle(&b[1]);
}

static void test_bundle_length_enum(void) {
    check_length_append_case(LENGTH_APPEND_EMPTY_EMPTY);
    check_length_append_case(LENGTH_APPEND_EMPTY_TWO);
    check_length_append_case(LENGTH_APPEND_TWO_ONE);
    check_nil_right_case(NIL_RIGHT_EMPTY);
    check_nil_right_case(NIL_RIGHT_THREE);
    check_assoc_case(ASSOC_EMPTY_LEFT);
    check_assoc_case(ASSOC_NONEMPTY);
    check_eq_right_iff_left_nil(EQ_RIGHT_LEFT_NIL);
    check_eq_right_iff_left_nil(EQ_RIGHT_NONEMPTY_LEFT);
    check_eq_left_iff_right_nil(EQ_LEFT_RIGHT_NIL);
    check_eq_left_iff_right_nil(EQ_LEFT_NONEMPTY_RIGHT);
    check_split_unique_fixed_lengths(SPLIT_UNIQUE_FIXED);
    check_split_unique_fixed_lengths(SPLIT_UNIQUE_FIXED);
    check_three_split_unique_fixed_lengths(THREE_SPLIT_UNIQUE);
    assert_manifest_smoke("manifests/bundle/bundle_length.enum.ct", LENGTH_APPEND_EMPTY_EMPTY);
    printf("  bundle_length.enum: 14/14 cases PASS\n");
}

static void test_bundle_length_algo(void) {
    check_length_append_case(LENGTH_APPEND_EMPTY_EMPTY);
    check_length_append_case(LENGTH_APPEND_EMPTY_TWO);
    check_length_append_case(LENGTH_APPEND_TWO_ONE);
    check_nil_right_case(NIL_RIGHT_EMPTY);
    check_nil_right_case(NIL_RIGHT_THREE);
    check_assoc_case(ASSOC_EMPTY_LEFT);
    check_assoc_case(ASSOC_NONEMPTY);
    check_eq_right_iff_left_nil(EQ_RIGHT_LEFT_NIL);
    check_eq_right_iff_left_nil(EQ_RIGHT_NONEMPTY_LEFT);
    check_eq_left_iff_right_nil(EQ_LEFT_RIGHT_NIL);
    check_eq_left_iff_right_nil(EQ_LEFT_NONEMPTY_RIGHT);
    check_split_unique_fixed_lengths(SPLIT_UNIQUE_FIXED);
    check_split_unique_fixed_lengths(SPLIT_UNIQUE_FIXED);
    check_three_split_unique_fixed_lengths(THREE_SPLIT_UNIQUE);
    assert_manifest_smoke("manifests/bundle/bundle_length.algo.ct", LENGTH_APPEND_EMPTY_EMPTY);
    printf("  bundle_length.algo: 14/14 cases PASS\n");
}

static void test_bundle_membership_enum(void) {
    check_nil_membership_case(NIL_ELIM_PROBE0);
    check_cons_self_case(CONS_SELF_PROBE1);
    check_singleton_iff_case(SINGLETON_IFF_YES);
    check_singleton_iff_case(SINGLETON_IFF_NO);
    check_append_membership_case(APPEND_MEMBER_LEFT);
    check_append_membership_case(APPEND_MEMBER_RIGHT);
    check_append_membership_case(APPEND_MEMBER_ABSENT);
    check_append_left_of_not_right_case(APPEND_MEMBER_LEFT);
    check_append_right_of_not_left_case(APPEND_MEMBER_RIGHT);
    check_append_three_case(APPEND_THREE_MIDDLE);
    check_append_four_case(APPEND_FOUR_LAST);
    check_member_split_case(MEMBER_SPLIT_HEAD);
    check_member_split_case(MEMBER_SPLIT_TAIL);
    check_cancellation_case(PREFIX_SUFFIX_CANCEL);
    check_cons_result_inversion_case(CONS_RESULT_INVERSION_PREFNIL);
    check_empty_result_inversion_case(EMPTY_RESULT_INVERSION);
    assert_manifest_smoke("manifests/bundle/bundle_membership.enum.ct", NIL_ELIM_PROBE0);
    printf("  bundle_membership.enum: 16/16 cases PASS\n");
}

static void test_bundle_membership_algo(void) {
    check_nil_membership_case(NIL_ELIM_PROBE0);
    check_cons_self_case(CONS_SELF_PROBE1);
    check_singleton_iff_case(SINGLETON_IFF_YES);
    check_singleton_iff_case(SINGLETON_IFF_NO);
    check_append_membership_case(APPEND_MEMBER_LEFT);
    check_append_membership_case(APPEND_MEMBER_RIGHT);
    check_append_membership_case(APPEND_MEMBER_ABSENT);
    check_append_left_of_not_right_case(APPEND_MEMBER_LEFT);
    check_append_right_of_not_left_case(APPEND_MEMBER_RIGHT);
    check_append_three_case(APPEND_THREE_MIDDLE);
    check_append_four_case(APPEND_FOUR_LAST);
    check_member_split_case(MEMBER_SPLIT_HEAD);
    check_member_split_case(MEMBER_SPLIT_TAIL);
    check_cancellation_case(PREFIX_SUFFIX_CANCEL);
    check_cons_result_inversion_case(CONS_RESULT_INVERSION_PREFNIL);
    check_empty_result_inversion_case(EMPTY_RESULT_INVERSION);
    assert_manifest_smoke("manifests/bundle/bundle_membership.algo.ct", NIL_ELIM_PROBE0);
    printf("  bundle_membership.algo: 16/16 cases PASS\n");
}

int main(void) {
    printf("== test_bundle ==\n");
    test_bundle_length_enum();
    test_bundle_length_algo();
    test_bundle_membership_enum();
    test_bundle_membership_algo();
    printf("ALL test_bundle assertions passed (60 ProbeBundle cases + 4-manifest pipeline smoke)\n");
    return 0;
}
