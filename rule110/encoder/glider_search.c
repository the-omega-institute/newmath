#include "rule110.h"

#include <errno.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char ETHER[] = "00010011011111";
enum { ETHER_PERIOD = 14, SIDE_ETHER_PERIODS = 16 };

static int ether_cell(size_t pos) {
    return ETHER[pos % ETHER_PERIOD] == '1';
}

static void fill_ether(uint8_t *cells, size_t len) {
    for (size_t i = 0; i < len; i++) {
        cells[i] = (uint8_t)ether_cell(i);
    }
}

static void place_seed(uint8_t *cells, size_t pos, uint64_t seed, int width) {
    for (int i = 0; i < width; i++) {
        int bit = (int)((seed >> (unsigned)(width - 1 - i)) & 1u);
        cells[pos + (size_t)i] = (uint8_t)bit;
    }
}

static void print_seed(uint64_t seed, int width) {
    for (int i = 0; i < width; i++) {
        int bit = (int)((seed >> (unsigned)(width - 1 - i)) & 1u);
        putchar(bit ? '1' : '0');
    }
}

static void format_seed(uint64_t seed, int width, char *out, size_t out_len) {
    if (out_len == 0) {
        return;
    }
    if ((size_t)width + 1u > out_len) {
        fprintf(stderr, "internal error: seed buffer too small\n");
        exit(1);
    }
    for (int i = 0; i < width; i++) {
        int bit = (int)((seed >> (unsigned)(width - 1 - i)) & 1u);
        out[i] = bit ? '1' : '0';
    }
    out[width] = '\0';
}

static bool seed_equals_at(const uint8_t *cells, size_t pos, uint64_t seed, int width) {
    for (int i = 0; i < width; i++) {
        int bit = (int)((seed >> (unsigned)(width - 1 - i)) & 1u);
        if (cells[pos + (size_t)i] != (uint8_t)bit) {
            return false;
        }
    }
    return true;
}

static bool quiet_ether_edges(const uint8_t *cells, const uint8_t *ether_control, size_t len, int steps) {
    size_t edge = (size_t)steps + ETHER_PERIOD;
    if (2 * edge >= len) {
        edge = len / 4;
    }

    for (size_t i = 0; i < edge; i++) {
        if (cells[i] != ether_control[i]) {
            return false;
        }
        size_t right = len - 1 - i;
        if (cells[right] != ether_control[right]) {
            return false;
        }
    }
    return true;
}

static bool same_shifted_perturbation(const uint8_t *before,
                                      const uint8_t *after,
                                      const uint8_t *ether_after,
                                      size_t len,
                                      int dx) {
    for (size_t i = 0; i < len; i++) {
        bool after_diff = after[i] != ether_after[i];
        int64_t src = (int64_t)i - (int64_t)dx;
        bool before_diff = false;
        if (src >= 0 && src < (int64_t)len) {
            before_diff = before[(size_t)src] != (uint8_t)ether_cell((size_t)src);
        }
        if (after_diff != before_diff) {
            return false;
        }
    }
    return true;
}

static bool nontrivial_seed(uint64_t seed, int width, int phase) {
    if (seed == 0) {
        return false;
    }

    bool is_ether = true;
    for (int i = 0; i < width; i++) {
        int bit = (int)((seed >> (unsigned)(width - 1 - i)) & 1u);
        if (bit != ether_cell((size_t)(phase + i))) {
            is_ether = false;
            break;
        }
    }
    return !is_ether;
}

struct Candidate {
    uint64_t seed;
    int phase;
    int diff_count;
    int diff_span;
    bool exact;
    bool valid;
};

static bool better_candidate(struct Candidate lhs, struct Candidate rhs) {
    if (!rhs.valid) {
        return true;
    }
    if (lhs.exact != rhs.exact) {
        return lhs.exact;
    }
    if (lhs.diff_span != rhs.diff_span) {
        return lhs.diff_span < rhs.diff_span;
    }
    if (lhs.diff_count != rhs.diff_count) {
        return lhs.diff_count < rhs.diff_count;
    }
    if (lhs.seed != rhs.seed) {
        return lhs.seed < rhs.seed;
    }
    return lhs.phase < rhs.phase;
}

static bool verify_seed(uint64_t seed,
                        int width,
                        int steps,
                        int dx,
                        int phase,
                        struct Candidate *candidate) {
    const size_t left_guard = (size_t)SIDE_ETHER_PERIODS * ETHER_PERIOD;
    const size_t right_guard = left_guard;
    const size_t seed_pos = left_guard + (size_t)phase;
    const size_t len = left_guard + ETHER_PERIOD + (size_t)width + right_guard;
    int64_t new_pos_signed = (int64_t)seed_pos + (int64_t)dx;
    if (new_pos_signed < 0 || new_pos_signed + width > (int64_t)len) {
        return false;
    }

    uint8_t *before = (uint8_t *)malloc(len);
    uint8_t *after = (uint8_t *)malloc(len);
    uint8_t *ether_control = (uint8_t *)malloc(len);
    if (before == NULL || after == NULL || ether_control == NULL) {
        perror("malloc");
        free(before);
        free(after);
        free(ether_control);
        exit(1);
    }

    fill_ether(before, len);
    fill_ether(ether_control, len);
    place_seed(before, seed_pos, seed, width);
    memcpy(after, before, len);

    r110_run_n_steps(after, len, (size_t)steps);
    r110_run_n_steps(ether_control, len, (size_t)steps);

    int diff_count = 0;
    int first_diff = -1;
    int last_diff = -1;
    for (size_t i = 0; i < len; i++) {
        if (after[i] != ether_control[i]) {
            if (first_diff < 0) {
                first_diff = (int)i;
            }
            last_diff = (int)i;
            diff_count++;
        }
    }

    bool ok = nontrivial_seed(seed, width, phase)
        && seed_equals_at(after, (size_t)new_pos_signed, seed, width)
        && quiet_ether_edges(after, ether_control, len, steps);
    bool exact = ok
        && same_shifted_perturbation(before, after, ether_control, len, dx);
    if (ok) {
        candidate->seed = seed;
        candidate->phase = phase;
        candidate->diff_count = diff_count;
        candidate->diff_span = last_diff >= first_diff ? last_diff - first_diff + 1 : 0;
        candidate->exact = exact;
        candidate->valid = true;
    }

    free(before);
    free(after);
    free(ether_control);
    return ok;
}

static bool parse_int_arg(const char *text, const char *name, int *out) {
    char *end = NULL;
    errno = 0;
    long value = strtol(text, &end, 10);
    if (errno != 0 || end == text || *end != '\0' || value < INT32_MIN || value > INT32_MAX) {
        fprintf(stderr, "invalid %s: %s\n", name, text);
        return false;
    }
    *out = (int)value;
    return true;
}

int main(int argc, char **argv) {
    if (argc != 5) {
        fprintf(stderr, "usage: %s <glider_name> <width> <period_t> <period_x>\n", argv[0]);
        return 2;
    }

    const char *name = argv[1];
    int width = 0;
    int steps = 0;
    int dx = 0;
    if (!parse_int_arg(argv[2], "width", &width)
        || !parse_int_arg(argv[3], "period_t", &steps)
        || !parse_int_arg(argv[4], "period_x", &dx)) {
        return 2;
    }
    if (width <= 0 || width > 30 || steps < 0) {
        fprintf(stderr, "invalid search bounds: width must be 1..30 and period_t must be nonnegative\n");
        return 2;
    }

    uint64_t limit = UINT64_C(1) << (unsigned)width;
    unsigned long found = 0;
    unsigned long exact_found = 0;
    struct Candidate best = {0};
    printf("# glider=%s width=%d period=(%d,%d) side_ether_periods=%d\n",
           name,
           width,
           steps,
           dx,
           SIDE_ETHER_PERIODS);

    for (uint64_t seed = 0; seed < limit; seed++) {
        for (int phase = 0; phase < ETHER_PERIOD; phase++) {
            struct Candidate candidate = {0};
            if (!verify_seed(seed, width, steps, dx, phase, &candidate)) {
                continue;
            }
            found++;
            if (candidate.exact) {
                exact_found++;
            }
            printf("%s %d %d %d ", name, width, steps, dx);
            print_seed(seed, width);
            printf(" phase=%d class=%s diff_count=%d diff_span=%d\n",
                   phase,
                   candidate.exact ? "exact" : "window",
                   candidate.diff_count,
                   candidate.diff_span);
            if (better_candidate(candidate, best)) {
                best = candidate;
            }
        }
    }

    printf("# candidates=%lu\n", found);
    printf("# exact_candidates=%lu\n", exact_found);
    if (best.valid) {
        char seed_text[32];
        format_seed(best.seed, width, seed_text, sizeof(seed_text));
        printf("# best %s seed=%s phase=%d class=%s diff_count=%d diff_span=%d\n",
               name,
               seed_text,
               best.phase,
               best.exact ? "exact" : "window",
               best.diff_count,
               best.diff_span);
    }
    return found == 0 ? 1 : 0;
}
