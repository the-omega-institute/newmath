#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const uint8_t RULE110_TABLE[8] = {0, 1, 1, 1, 0, 1, 1, 0};

static uint8_t rule110_cell(uint8_t left, uint8_t self, uint8_t right) {
    return RULE110_TABLE[(left << 2) | (self << 1) | right];
}

static int is_binary_string(const char *s) {
    if (s == NULL || s[0] == '\0') return 0;
    for (size_t i = 0; s[i] != '\0'; i++) {
        if (s[i] != '0' && s[i] != '1') return 0;
    }
    return 1;
}

static int parse_size_arg(const char *s, size_t *out) {
    char *end = NULL;
    unsigned long value;

    if (s == NULL || s[0] == '\0') return 0;
    value = strtoul(s, &end, 10);
    if (end == s || *end != '\0') return 0;
    *out = (size_t)value;
    return 1;
}

static int extend_preimage(const uint8_t *target,
                           size_t len,
                           uint8_t *candidate,
                           size_t next_index) {
    if (next_index == len) {
        return rule110_cell(candidate[len - 2], candidate[len - 1], 0) ==
               target[len - 1];
    }

    for (uint8_t bit = 0; bit <= 1; bit++) {
        candidate[next_index] = bit;
        if (rule110_cell(candidate[next_index - 2],
                         candidate[next_index - 1],
                         candidate[next_index]) != target[next_index - 1]) {
            continue;
        }
        if (extend_preimage(target, len, candidate, next_index + 1)) {
            return 1;
        }
    }

    return 0;
}

static int find_one_step_preimage(const uint8_t *target,
                                  size_t len,
                                  uint8_t *out) {
    if (len < 2) return 0;

    for (uint8_t first = 0; first <= 1; first++) {
        for (uint8_t second = 0; second <= 1; second++) {
            out[0] = first;
            out[1] = second;
            if (extend_preimage(target, len, out, 2)) return 1;
        }
    }

    return 0;
}

static void print_bits(const uint8_t *bits, size_t len) {
    for (size_t i = 0; i < len; i++) putchar(bits[i] ? '1' : '0');
}

int main(int argc, char **argv) {
    const char *case_name;
    const char *input_bits;
    size_t initial_len = 48;
    size_t payload_start = 16;
    size_t payload_len;
    uint8_t *target = NULL;
    uint8_t *initial = NULL;

    if (argc != 3 && argc != 5) {
        fprintf(stderr,
                "usage: %s <case-name> <input-bits> [initial-length payload-start]\n",
                argv[0]);
        return 2;
    }

    case_name = argv[1];
    input_bits = argv[2];
    if (!is_binary_string(input_bits)) {
        fprintf(stderr, "reject: input must be a nonempty bit string\n");
        return 2;
    }
    payload_len = strlen(input_bits);

    if (argc == 5) {
        if (!parse_size_arg(argv[3], &initial_len) ||
            !parse_size_arg(argv[4], &payload_start)) {
            fprintf(stderr, "reject: invalid numeric argument\n");
            return 2;
        }
    }

    if (payload_start > initial_len || payload_len > initial_len - payload_start) {
        fprintf(stderr, "reject: payload window exceeds initial length\n");
        return 2;
    }

    target = (uint8_t *)calloc(initial_len ? initial_len : 1, sizeof(uint8_t));
    initial = (uint8_t *)malloc(initial_len ? initial_len : 1);
    if (target == NULL || initial == NULL) {
        fprintf(stderr, "reject: allocation failure\n");
        free(target);
        free(initial);
        return 1;
    }

    for (size_t i = 0; i < payload_len; i++) {
        target[payload_start + i] = (uint8_t)(input_bits[i] == '1');
    }

    if (!find_one_step_preimage(target, initial_len, initial)) {
        fprintf(stderr,
                "reject: no one-step Rule 110 preimage found for requested payload\n");
        free(target);
        free(initial);
        return 1;
    }

    printf("case %s: input=%s ; rule110_initial=", case_name, input_bits);
    print_bits(initial, initial_len);
    printf(" ; steps=1 ; payload_start=%zu ; payload_len=%zu ; expected_payload=",
           payload_start,
           payload_len);
    print_bits(target + payload_start, payload_len);
    printf(" ; expected_reflexive=yes ; encoding=groundcompiler_event_pair ; construction=one_step_preimage\n");

    free(target);
    free(initial);
    return 0;
}
