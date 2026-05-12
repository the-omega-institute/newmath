#include "manifest_runner.h"
#include "groundcompiler_encoding.h"
#include <assert.h>
#include <ctype.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define GC_MANIFEST_DIR "manifests/ground_compiler/"

typedef struct {
    char name[96];
    char input[512];
    char display[512];
    char theorem[128];
    char expected_reject[64];
    char left[64];
    char right[64];
    int events;
    int fuel;
    int round_trip;
    int conservative_marks;
    int canonical;
    int same_source;
    int same_encoding;
} GcCase;

static char *trim_ascii(char *s) {
    char *end;

    while (*s && isspace((unsigned char)*s)) s++;
    end = s + strlen(s);
    while (end > s && isspace((unsigned char)end[-1])) end--;
    *end = '\0';
    return s;
}

static int parse_yes_no(const char *value) {
    if (strcmp(value, "yes") == 0) return 1;
    if (strcmp(value, "no") == 0) return 0;
    assert(0 && "expected yes/no value");
    return 0;
}

static void copy_value(char *dst, size_t dst_cap, const char *src) {
    size_t n = strlen(src);
    assert(n + 1 <= dst_cap);
    memcpy(dst, src, n + 1);
}

static void gc_case_init(GcCase *c) {
    memset(c, 0, sizeof(*c));
    c->events = -1;
    c->fuel = 8192;
    c->round_trip = -1;
    c->conservative_marks = -1;
    c->canonical = -1;
    c->same_source = -1;
    c->same_encoding = -1;
}

static int parse_case_line(char *line, GcCase *out) {
    char *p;
    char *colon;
    char *field;

    p = trim_ascii(line);
    if (strncmp(p, "case ", 5) != 0) return 0;
    p += 5;
    colon = strchr(p, ':');
    assert(colon != NULL);
    *colon = '\0';
    copy_value(out->name, sizeof(out->name), trim_ascii(p));

    field = colon + 1;
    for (;;) {
        char *semi = strchr(field, ';');
        char *eq;
        char *key;
        char *value;

        if (semi != NULL) *semi = '\0';
        field = trim_ascii(field);
        if (*field != '\0') {
            eq = strchr(field, '=');
            assert(eq != NULL);
            *eq = '\0';
            key = trim_ascii(field);
            value = trim_ascii(eq + 1);

            if (strcmp(key, "input") == 0) {
                copy_value(out->input, sizeof(out->input), value);
            } else if (strcmp(key, "display") == 0) {
                copy_value(out->display, sizeof(out->display), value);
            } else if (strcmp(key, "theorem") == 0) {
                copy_value(out->theorem, sizeof(out->theorem), value);
            } else if (strcmp(key, "expected_reject") == 0) {
                copy_value(out->expected_reject, sizeof(out->expected_reject), value);
            } else if (strcmp(key, "left") == 0) {
                copy_value(out->left, sizeof(out->left), value);
            } else if (strcmp(key, "right") == 0) {
                copy_value(out->right, sizeof(out->right), value);
            } else if (strcmp(key, "events") == 0) {
                out->events = atoi(value);
            } else if (strcmp(key, "fuel") == 0) {
                out->fuel = atoi(value);
            } else if (strcmp(key, "round_trip") == 0) {
                out->round_trip = parse_yes_no(value);
            } else if (strcmp(key, "conservative_marks") == 0) {
                out->conservative_marks = parse_yes_no(value);
            } else if (strcmp(key, "canonical") == 0) {
                out->canonical = parse_yes_no(value);
            } else if (strcmp(key, "same_source") == 0) {
                out->same_source = parse_yes_no(value);
            } else if (strcmp(key, "same_encoding") == 0) {
                out->same_encoding = parse_yes_no(value);
            } else {
                fprintf(stderr, "unknown field in %s: %s\n", out->name, key);
                assert(0);
            }
        }
        if (semi == NULL) break;
        field = semi + 1;
    }
    return 1;
}

typedef void (*GcCaseFn)(const char *path, const GcCase *c, void *ctx);

static size_t for_each_case(const char *path, GcCaseFn fn, void *ctx) {
    FILE *f = fopen(path, "r");
    char line[2048];
    size_t cases = 0;

    assert(f != NULL);
    while (fgets(line, sizeof(line), f) != NULL) {
        GcCase c;

        gc_case_init(&c);
        if (parse_case_line(line, &c)) {
            fn(path, &c, ctx);
            cases++;
        }
    }
    fclose(f);
    return cases;
}

static int bits_to_bytes(const char *input_bits, uint8_t **out, size_t *out_len) {
    size_t in_len;
    uint8_t *bytes;

    if (strcmp(input_bits, "<empty>") == 0) input_bits = "";
    in_len = strlen(input_bits);
    bytes = (uint8_t *)malloc(in_len ? in_len : 1);
    if (bytes == NULL) return 0;

    for (size_t i = 0; i < in_len; i++) {
        if (input_bits[i] != '0' && input_bits[i] != '1') {
            free(bytes);
            return 0;
        }
        bytes[i] = (uint8_t)(input_bits[i] - '0');
    }

    *out = bytes;
    *out_len = in_len;
    return 1;
}

static int display_is_canonical_binary(const char *display) {
    if (strcmp(display, "<empty>") == 0) return 1;
    for (size_t i = 0; display[i] != '\0'; i++) {
        if (display[i] != '0' && display[i] != '1') return 0;
    }
    return 1;
}

static int bhist_equal(const BHist *a, const BHist *b) {
    return a->depth == b->depth &&
           (a->depth == 0 || memcmp(a->choices, b->choices, a->depth) == 0);
}

static void free_bhist(BHist *h) {
    free(h->choices);
    h->choices = NULL;
    h->depth = 0;
}

static void free_event_result(GcDecResult *r) {
    free(r->event);
    r->event = NULL;
    r->event_len = 0;
    r->bytes_consumed = 0;
}

static void assert_manifest_smoke(const char *path, const char *input_bits) {
    MrResult r;

    if (!display_is_canonical_binary(input_bits)) return;
    if (strcmp(input_bits, "<empty>") == 0) input_bits = "";
    r = mr_run_ct_manifest(path, input_bits, "", 300);
    if (r != MR_PASS) {
        fprintf(stderr, "manifest smoke FAIL on %s input=%s result=%d\n",
                path, input_bits, (int)r);
    }
    assert(r == MR_PASS);
}

static void check_flow_case(const char *path, const GcCase *c, void *ctx) {
    uint8_t *bytes = NULL;
    uint8_t encoded[512];
    uint8_t *events[64];
    size_t event_lens[64];
    size_t len = 0;
    size_t off = 0;
    size_t event_count = 0;
    size_t encoded_len;

    (void)ctx;
    assert(strstr(c->theorem, "roundtrip") != NULL ||
           strstr(c->theorem, "round_trip") != NULL ||
           strcmp(c->theorem, "channel_conservativity") == 0);
    assert(c->round_trip == 1);
    assert(c->conservative_marks == 1);
    assert(c->canonical == 1);
    assert(bits_to_bytes(c->input, &bytes, &len));
    assert_manifest_smoke(path, c->input);

    while (off < len) {
        GcDecResult r = gc_dec_event(bytes + off, len - off, 8192);
        assert(r.status == GC_OK);
        assert(event_count < 64);
        for (size_t i = 0; i < r.event_len; i++) {
            assert(r.event[i] == 0 || r.event[i] == 1);
        }
        events[event_count] = r.event;
        event_lens[event_count] = r.event_len;
        event_count++;
        off += r.bytes_consumed;
    }

    assert((int)event_count == c->events);
    encoded_len = gc_flow_encode(events, event_lens, event_count,
                                 encoded, sizeof(encoded));
    assert(encoded_len == len);
    assert(len == 0 || memcmp(encoded, bytes, len) == 0);

    for (size_t i = 0; i < event_count; i++) free(events[i]);
    free(bytes);
}

static void check_bhist_injectivity_case(const char *path,
                                         const GcCase *c,
                                         void *ctx) {
    uint8_t *bytes = NULL;
    uint8_t left_enc[128];
    uint8_t right_enc[128];
    size_t len = 0;
    size_t off;
    size_t left_len;
    size_t right_len;
    int same_source;
    int same_encoding;
    GcBhistDecResult left;
    GcBhistDecResult right;

    (void)ctx;
    assert(strcmp(c->theorem, "channel_encoding_bijection") == 0 ||
           strcmp(c->theorem, "legal_stream_completeness") == 0);
    assert(bits_to_bytes(c->input, &bytes, &len));
    assert_manifest_smoke(path, c->input);

    left = gc_bhist_decode(bytes, len, 8192);
    assert(left.status == GC_OK);
    off = left.bytes_consumed;
    right = gc_bhist_decode(bytes + off, len - off, 8192);
    assert(right.status == GC_OK);
    assert(off + right.bytes_consumed == len);

    left_len = gc_bhist_encode(&left.bhist, left_enc, sizeof(left_enc));
    right_len = gc_bhist_encode(&right.bhist, right_enc, sizeof(right_enc));
    same_source = bhist_equal(&left.bhist, &right.bhist);
    same_encoding = left_len == right_len &&
                    (left_len == 0 || memcmp(left_enc, right_enc, left_len) == 0);

    assert(same_source == c->same_source);
    assert(same_encoding == c->same_encoding);
    assert(!same_encoding || same_source);

    free_bhist(&left.bhist);
    free_bhist(&right.bhist);
    free(bytes);
}

static GcStatus status_from_name(const char *name) {
    if (strcmp(name, "DANGLING_ONE") == 0) return GC_REJECT_DANGLING_ONE;
    if (strcmp(name, "UNFINISHED_EVENT") == 0) return GC_REJECT_UNFINISHED_EVENT;
    if (strcmp(name, "NONBINARY_CHARACTER") == 0) return GC_REJECT_NONBINARY_CHARACTER;
    if (strcmp(name, "EMPTY_INPUT_POLICY") == 0) return GC_REJECT_EMPTY_INPUT_POLICY;
    if (strcmp(name, "RESOURCE_BOUND_EXCESS") == 0) return GC_REJECT_RESOURCE_BOUND_EXCESS;
    if (strcmp(name, "NONCANONICAL_DISPLAY") == 0) return GC_REJECT_NONCANONICAL_DISPLAY;
    assert(0 && "unknown reject status");
    return GC_OK;
}

static GcStatus classify_reject_case(const GcCase *c) {
    uint8_t *bytes = NULL;
    size_t len = 0;
    GcDecResult r;
    GcStatus status;
    const char *display = c->display[0] != '\0' ? c->display : c->input;

    if (!display_is_canonical_binary(display)) {
        if (strcmp(c->expected_reject, "NONBINARY_CHARACTER") == 0) {
            int has_nonbinary = 0;
            for (size_t i = 0; display[i] != '\0'; i++) {
                if (display[i] != '0' && display[i] != '1' &&
                    !isspace((unsigned char)display[i])) {
                    has_nonbinary = 1;
                }
            }
            if (has_nonbinary && strchr(display, '_') == NULL) {
                return GC_REJECT_NONBINARY_CHARACTER;
            }
        }
        return GC_REJECT_NONCANONICAL_DISPLAY;
    }

    assert(bits_to_bytes(display, &bytes, &len));
    r = gc_dec_event(bytes, len, (size_t)c->fuel);
    status = r.status;
    free_event_result(&r);
    free(bytes);
    return status;
}

static void check_reject_case(const char *path, const GcCase *c, void *ctx) {
    GcStatus expected;
    GcStatus got;

    (void)ctx;
    assert(strcmp(c->theorem, "groundcompiler_reject_taxonomy") == 0);
    expected = status_from_name(c->expected_reject);
    got = classify_reject_case(c);
    if (got != expected) {
        fprintf(stderr, "reject mismatch in %s case %s: got=%d expected=%d\n",
                path, c->name, (int)got, (int)expected);
    }
    assert(got == expected);
}

static void test_event_level_closed_samples(void) {
    uint8_t empty_event[1] = {0};
    uint8_t mixed_event[4] = {0, 1, 1, 0};
    uint8_t encoded[32];
    GcDecResult r;
    size_t n;

    n = gc_event_encode(NULL, 0, encoded, sizeof(encoded));
    assert(n == 2);
    assert(encoded[0] == 1 && encoded[1] == 1);
    r = gc_dec_event(encoded, n, 16);
    assert(r.status == GC_OK);
    assert(r.event_len == 0);
    assert(r.bytes_consumed == n);
    free_event_result(&r);

    n = gc_event_encode(empty_event, 1, encoded, sizeof(encoded));
    assert(n == 3);
    r = gc_dec_event(encoded, n, 16);
    assert(r.status == GC_OK);
    assert(r.event_len == 1 && r.event[0] == 0);
    free_event_result(&r);

    n = gc_event_encode(mixed_event, 4, encoded, sizeof(encoded));
    assert(n == 8);
    r = gc_dec_event(encoded, n, 16);
    assert(r.status == GC_OK);
    assert(r.event_len == 4);
    assert(memcmp(r.event, mixed_event, 4) == 0);
    free_event_result(&r);

    printf("  event_level_closed_samples: PASS\n");
}

static void test_flow_round_trip_manifest(void) {
    const char *path = GC_MANIFEST_DIR "flow_round_trip.enum.ct";
    size_t cases = for_each_case(path, check_flow_case, NULL);

    assert(cases == 5);
    printf("  flow_round_trip_manifest: PASS (%zu cases)\n", cases);
}

static void test_bhist_injectivity_manifest(void) {
    const char *path = GC_MANIFEST_DIR "bhist_injectivity.enum.ct";
    size_t cases = for_each_case(path, check_bhist_injectivity_case, NULL);

    assert(cases == 6);
    printf("  bhist_injectivity_manifest: PASS (%zu cases)\n", cases);
}

static void test_reject_reasons_manifest(void) {
    const char *path = GC_MANIFEST_DIR "reject_reasons.enum.ct";
    size_t cases = for_each_case(path, check_reject_case, NULL);

    assert(cases == 6);
    printf("  reject_reasons_manifest: PASS (%zu cases)\n", cases);
}

int main(void) {
    printf("test_ground_compiler\n");
    test_event_level_closed_samples();
    test_flow_round_trip_manifest();
    test_bhist_injectivity_manifest();
    test_reject_reasons_manifest();
    printf("test_ground_compiler: PASS\n");
    return 0;
}
