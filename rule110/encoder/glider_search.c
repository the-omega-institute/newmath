#include "rule110.h"

#include <errno.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char ETHER[] = "00010011011111";
enum { ETHER_PERIOD = 14, SIDE_ETHER_PERIODS = 32, MULTIPERIOD_CHECKS = 3 };

static int ether_cell(size_t pos) {
    return ETHER[pos % ETHER_PERIOD] == '1';
}

static void fill_ether(uint8_t *cells, size_t len) {
    for (size_t i = 0; i < len; i++) {
        cells[i] = (uint8_t)ether_cell(i);
    }
}

static void run_steps_with_buffer(uint8_t *cells, uint8_t *scratch, size_t len, int steps) {
    for (int step = 0; step < steps; step++) {
        memcpy(scratch, cells, len);
        for (size_t i = 0; i < len; i++) {
            uint8_t left = i == 0 ? 0 : scratch[i - 1];
            uint8_t self = scratch[i];
            uint8_t right = i + 1 == len ? 0 : scratch[i + 1];
            cells[i] = (left || self || right) && !(left && self && right) && !(left && !self && !right);
        }
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

struct Candidate {
    uint64_t seed;
    int width;
    int phase;
    int diff_count;
    int diff_span;
    bool exact;
    bool valid;
};

struct Work {
    uint8_t *before;
    uint8_t *after;
    uint8_t *ether_control;
    uint8_t *ether_initial;
    uint8_t *scratch;
    size_t len;
};

static void free_work(struct Work *work) {
    free(work->before);
    free(work->after);
    free(work->ether_control);
    free(work->ether_initial);
    free(work->scratch);
    work->before = NULL;
    work->after = NULL;
    work->ether_control = NULL;
    work->ether_initial = NULL;
    work->scratch = NULL;
    work->len = 0;
}

static void ensure_work(struct Work *work, size_t len) {
    if (work->len >= len) {
        return;
    }
    free_work(work);
    work->before = (uint8_t *)malloc(len);
    work->after = (uint8_t *)malloc(len);
    work->ether_control = (uint8_t *)malloc(len);
    work->ether_initial = (uint8_t *)malloc(len);
    work->scratch = (uint8_t *)malloc(len);
    if (work->before == NULL || work->after == NULL || work->ether_control == NULL
        || work->ether_initial == NULL || work->scratch == NULL) {
        perror("malloc");
        free_work(work);
        exit(1);
    }
    work->len = len;
}

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
    if (lhs.width != rhs.width) {
        return lhs.width < rhs.width;
    }
    return lhs.phase < rhs.phase;
}

static void diff_stats(const uint8_t *cells,
                       const uint8_t *ether_control,
                       size_t len,
                       int *diff_count,
                       int *diff_span) {
    int first_diff = -1;
    int last_diff = -1;
    *diff_count = 0;
    for (size_t i = 0; i < len; i++) {
        if (cells[i] != ether_control[i]) {
            if (first_diff < 0) {
                first_diff = (int)i;
            }
            last_diff = (int)i;
            (*diff_count)++;
        }
    }
    *diff_span = last_diff >= first_diff ? last_diff - first_diff + 1 : 0;
}

static bool verify_seed(uint64_t seed,
                        int width,
                        int steps,
                        int dx,
                        int phase,
                        struct Work *work,
                        struct Candidate *candidate) {
    const size_t left_guard = (size_t)SIDE_ETHER_PERIODS * ETHER_PERIOD;
    const size_t right_guard = left_guard;
    const size_t seed_pos = left_guard + (size_t)phase;
    const size_t len = left_guard + ETHER_PERIOD + (size_t)width + right_guard;
    ensure_work(work, len);

    uint8_t *before = work->before;
    uint8_t *after = work->after;
    uint8_t *ether_control = work->ether_control;
    uint8_t *ether_initial = work->ether_initial;
    uint8_t *scratch = work->scratch;

    fill_ether(before, len);
    fill_ether(ether_control, len);
    place_seed(before, seed_pos, seed, width);
    memcpy(after, before, len);
    fill_ether(ether_initial, len);

    int initial_diff_count = 0;
    int initial_diff_span = 0;
    diff_stats(before, ether_initial, len, &initial_diff_count, &initial_diff_span);

    bool window_all = initial_diff_count > 0;
    bool exact = initial_diff_count > 0;
    int diff_count = 0;
    int diff_span = 0;
    memcpy(after, before, len);
    fill_ether(ether_control, len);
    for (int multiple = 1; multiple <= MULTIPERIOD_CHECKS && (window_all || exact); multiple++) {
        int total_steps = steps * multiple;
        int total_dx = dx * multiple;
        int64_t shifted_pos = (int64_t)seed_pos + (int64_t)total_dx;
        if (shifted_pos < 0 || shifted_pos + width > (int64_t)len) {
            window_all = false;
            exact = false;
            break;
        }

        run_steps_with_buffer(after, scratch, len, steps);
        run_steps_with_buffer(ether_control, scratch, len, steps);

        if (multiple == 1) {
            diff_stats(after, ether_control, len, &diff_count, &diff_span);
        }

        bool window_ok = seed_equals_at(after, (size_t)shifted_pos, seed, width)
            && quiet_ether_edges(after, ether_control, len, total_steps);
        bool exact_ok = quiet_ether_edges(after, ether_control, len, total_steps)
            && same_shifted_perturbation(before, after, ether_control, len, total_dx);
        window_all = window_all && window_ok;
        exact = exact && exact_ok;
    }
    if (window_all || exact) {
        candidate->seed = seed;
        candidate->width = width;
        candidate->phase = phase;
        candidate->diff_count = diff_count;
        candidate->diff_span = diff_span;
        candidate->exact = exact;
        candidate->valid = true;
    }

    return window_all || exact;
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
    if (argc != 5 && argc != 7) {
        fprintf(stderr,
                "usage: %s <glider_name> <width> <period_t> <period_x> [--extended-width N]\n",
                argv[0]);
        return 2;
    }

    const char *name = argv[1];
    int width = 0;
    int steps = 0;
    int dx = 0;
    int extended_width = 0;
    if (!parse_int_arg(argv[2], "width", &width)
        || !parse_int_arg(argv[3], "period_t", &steps)
        || !parse_int_arg(argv[4], "period_x", &dx)) {
        return 2;
    }
    if (argc == 7) {
        if (strcmp(argv[5], "--extended-width") != 0
            || !parse_int_arg(argv[6], "extended_width", &extended_width)) {
            fprintf(stderr,
                    "usage: %s <glider_name> <width> <period_t> <period_x> [--extended-width N]\n",
                    argv[0]);
            return 2;
        }
    }
    if (width <= 0 || width > 30 || steps < 0 || extended_width < 0 || width + extended_width > 30) {
        fprintf(stderr, "invalid search bounds: width and extended width must stay in 1..30 and period_t must be nonnegative\n");
        return 2;
    }

    unsigned long found = 0;
    unsigned long exact_found = 0;
    struct Candidate best = {0};
    struct Work work = {0};
    printf("# glider=%s width=%d extended_width=%d period=(%d,%d) side_ether_periods=%d multiperiod=%d\n",
           name,
           width,
           extended_width,
           steps,
           dx,
           SIDE_ETHER_PERIODS,
           MULTIPERIOD_CHECKS);

    for (int seed_width = width; seed_width <= width + extended_width; seed_width++) {
        uint64_t limit = UINT64_C(1) << (unsigned)seed_width;
        for (uint64_t seed = 0; seed < limit; seed++) {
            for (int phase = 0; phase < ETHER_PERIOD; phase++) {
                struct Candidate candidate = {0};
                if (!verify_seed(seed, seed_width, steps, dx, phase, &work, &candidate)) {
                    continue;
                }
                found++;
                if (candidate.exact) {
                    exact_found++;
                }
                printf("%s %d %d %d ", name, seed_width, steps, dx);
                print_seed(seed, seed_width);
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
    }
    free_work(&work);

    printf("# candidates=%lu\n", found);
    printf("# exact_candidates=%lu\n", exact_found);
    if (best.valid) {
        char seed_text[32];
        format_seed(best.seed, best.width, seed_text, sizeof(seed_text));
        printf("# best %s width=%d seed=%s phase=%d class=%s diff_count=%d diff_span=%d\n",
               name,
               best.width,
               seed_text,
               best.phase,
               best.exact ? "exact" : "window",
               best.diff_count,
               best.diff_span);
    }
    return found == 0 ? 1 : 0;
}
