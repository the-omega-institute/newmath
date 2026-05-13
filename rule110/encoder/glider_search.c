#include "rule110.h"

#include <errno.h>
#include <inttypes.h>
#include <stdbool.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

static const char ETHER[] = "00010011011111";
enum {
    ETHER_PERIOD = 14,
    SIDE_ETHER_PERIODS = 32,
    MULTIPERIOD_CHECKS = 3,
    DEFAULT_MAX_EXTENDED_WIDTH = 8,
    HARD_MAX_EXTENDED_WIDTH = 16,
    MAX_SEED_WIDTH = 30,
    MAX_PERIOD_TRIALS = 16
};

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

static bool same_shifted_active_cells(const uint8_t *before,
                                      const uint8_t *after,
                                      const uint8_t *ether_before,
                                      const uint8_t *ether_after,
                                      size_t len,
                                      int dx) {
    for (size_t src = 0; src < len; src++) {
        if (before[src] != ether_before[src]) {
            int64_t dst = (int64_t)src + (int64_t)dx;
            if (dst < 0 || dst >= (int64_t)len) {
                return false;
            }
        }
    }
    for (size_t i = 0; i < len; i++) {
        bool after_diff = after[i] != ether_after[i];
        int64_t src = (int64_t)i - (int64_t)dx;
        bool before_diff = false;
        uint8_t before_cell = 0;
        if (src >= 0 && src < (int64_t)len) {
            before_diff = before[(size_t)src] != ether_before[(size_t)src];
            before_cell = before[(size_t)src];
        }
        if ((after_diff || before_diff) && (src < 0 || src >= (int64_t)len || after[i] != before_cell)) {
            return false;
        }
    }
    return true;
}

static bool tube_periodic_raw(uint8_t *rows,
                              uint8_t *ether_rows,
                              uint8_t *scratch,
                              size_t len,
                              int period_steps,
                              int period_dx,
                              int comparisons) {
    size_t row_count = (size_t)period_steps * (size_t)(comparisons + 1);
    if (row_count == 0) {
        return false;
    }

    for (size_t row = 1; row < row_count; row++) {
        memcpy(rows + row * len, rows + (row - 1u) * len, len);
        run_steps_with_buffer(rows + row * len, scratch, len, 1);
        memcpy(ether_rows + row * len, ether_rows + (row - 1u) * len, len);
        run_steps_with_buffer(ether_rows + row * len, scratch, len, 1);
    }

    for (int block = 0; block < comparisons; block++) {
        int total_steps = period_steps * (block + 1);
        if (!quiet_ether_edges(rows + (size_t)total_steps * len,
                               ether_rows + (size_t)total_steps * len,
                               len,
                               total_steps)) {
            return false;
        }
        for (int offset = 0; offset < period_steps; offset++) {
            size_t row_a = ((size_t)block * (size_t)period_steps + (size_t)offset) * len;
            size_t row_b = row_a + (size_t)period_steps * len;
            if (!same_shifted_active_cells(rows + row_a,
                                           rows + row_b,
                                           ether_rows + row_a,
                                           ether_rows + row_b,
                                           len,
                                           period_dx)) {
                return false;
            }
        }
    }
    return true;
}

struct Candidate {
    uint64_t seed;
    int width;
    int phase;
    int period_multiplier;
    int period_steps;
    int period_dx;
    int diff_count;
    int diff_span;
    bool exact;
    bool tube_exact;
    bool valid;
};

struct Work {
    uint8_t *before;
    uint8_t *after;
    uint8_t *ether_control;
    uint8_t *ether_initial;
    uint8_t *scratch;
    uint8_t *rows;
    uint8_t *ether_rows;
    size_t len;
    size_t history_len;
};

static void free_work(struct Work *work) {
    free(work->before);
    free(work->after);
    free(work->ether_control);
    free(work->ether_initial);
    free(work->scratch);
    free(work->rows);
    free(work->ether_rows);
    work->before = NULL;
    work->after = NULL;
    work->ether_control = NULL;
    work->ether_initial = NULL;
    work->scratch = NULL;
    work->rows = NULL;
    work->ether_rows = NULL;
    work->len = 0;
    work->history_len = 0;
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

static void ensure_history(struct Work *work, size_t history_len) {
    if (work->history_len >= history_len) {
        return;
    }
    free(work->rows);
    free(work->ether_rows);
    work->rows = (uint8_t *)malloc(history_len);
    work->ether_rows = (uint8_t *)malloc(history_len);
    if (work->rows == NULL || work->ether_rows == NULL) {
        perror("malloc");
        free_work(work);
        exit(1);
    }
    work->history_len = history_len;
}

static bool better_candidate(struct Candidate lhs, struct Candidate rhs) {
    if (!rhs.valid) {
        return true;
    }
    if (lhs.exact != rhs.exact) {
        return lhs.exact;
    }
    if (lhs.tube_exact != rhs.tube_exact) {
        return lhs.tube_exact;
    }
    if (lhs.period_multiplier != rhs.period_multiplier) {
        return lhs.period_multiplier < rhs.period_multiplier;
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
                        int period_steps,
                        int period_dx,
                        int period_multiplier,
                        int phase,
                        struct Work *work,
                        struct Candidate *candidate) {
    size_t guard = (size_t)SIDE_ETHER_PERIODS * ETHER_PERIOD;
    size_t dynamic_guard = (size_t)period_steps * (size_t)(MULTIPERIOD_CHECKS + 1)
        + (size_t)(period_dx < 0 ? -period_dx : period_dx) * (size_t)MULTIPERIOD_CHECKS
        + ETHER_PERIOD;
    if (dynamic_guard > guard) {
        guard = dynamic_guard;
    }
    const size_t left_guard = guard;
    const size_t right_guard = guard;
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
    bool raw_endpoints = initial_diff_count > 0;
    int diff_count = 0;
    int diff_span = 0;
    memcpy(after, before, len);
    fill_ether(ether_control, len);
    for (int multiple = 1;
         multiple <= MULTIPERIOD_CHECKS && (window_all || exact || raw_endpoints);
         multiple++) {
        int total_steps = period_steps * multiple;
        int total_dx = period_dx * multiple;
        int64_t shifted_pos = (int64_t)seed_pos + (int64_t)total_dx;
        if (shifted_pos < 0 || shifted_pos + width > (int64_t)len) {
            window_all = false;
        }

        run_steps_with_buffer(after, scratch, len, period_steps);
        run_steps_with_buffer(ether_control, scratch, len, period_steps);

        if (multiple == 1) {
            diff_stats(after, ether_control, len, &diff_count, &diff_span);
        }

        bool quiet_edges = quiet_ether_edges(after, ether_control, len, total_steps);
        bool window_ok = shifted_pos >= 0 && shifted_pos + width <= (int64_t)len
            && seed_equals_at(after, (size_t)shifted_pos, seed, width)
            && quiet_edges;
        bool exact_ok = quiet_edges
            && same_shifted_perturbation(before, after, ether_control, len, total_dx);
        bool raw_ok = quiet_edges
            && same_shifted_active_cells(before, after, ether_initial, ether_control, len, total_dx);
        window_all = window_all && window_ok;
        exact = exact && exact_ok;
        raw_endpoints = raw_endpoints && raw_ok;
    }
    bool tube_exact = false;
    if (!exact && raw_endpoints && period_steps > 0) {
        size_t row_count = (size_t)period_steps * (size_t)(MULTIPERIOD_CHECKS + 1);
        size_t history_len = row_count * len;
        ensure_history(work, history_len);
        memcpy(work->rows, before, len);
        memcpy(work->ether_rows, ether_initial, len);
        tube_exact = tube_periodic_raw(work->rows,
                                       work->ether_rows,
                                       scratch,
                                       len,
                                       period_steps,
                                       period_dx,
                                       MULTIPERIOD_CHECKS);
        exact = tube_exact;
    }
    if (window_all || exact) {
        candidate->seed = seed;
        candidate->width = width;
        candidate->phase = phase;
        candidate->period_multiplier = period_multiplier;
        candidate->period_steps = period_steps;
        candidate->period_dx = period_dx;
        candidate->diff_count = diff_count;
        candidate->diff_span = diff_span;
        candidate->exact = exact;
        candidate->tube_exact = tube_exact;
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

static void usage(const char *prog) {
    fprintf(stderr,
            "usage: %s <glider_name> <width> <period_t> <period_x> "
            "[--max-extended-width N] [--extended-width N] "
            "[--try-periods k1,k2,...] [--try-both-dx]\n",
            prog);
}

static bool parse_period_list(const char *text, int *periods, int *period_count) {
    const char *cursor = text;
    int count = 0;
    while (*cursor != '\0') {
        if (count >= MAX_PERIOD_TRIALS) {
            fprintf(stderr, "too many period trials; maximum is %d\n", MAX_PERIOD_TRIALS);
            return false;
        }
        char *end = NULL;
        errno = 0;
        long value = strtol(cursor, &end, 10);
        if (errno != 0 || end == cursor || value <= 0 || value > INT32_MAX) {
            fprintf(stderr, "invalid period multiplier list: %s\n", text);
            return false;
        }
        periods[count++] = (int)value;
        if (*end == '\0') {
            break;
        }
        if (*end != ',') {
            fprintf(stderr, "invalid period multiplier list: %s\n", text);
            return false;
        }
        cursor = end + 1;
        if (*cursor == '\0') {
            fprintf(stderr, "invalid period multiplier list: %s\n", text);
            return false;
        }
    }
    *period_count = count;
    return count > 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        usage(argv[0]);
        return 2;
    }

    const char *name = argv[1];
    int width = 0;
    int steps = 0;
    int dx = 0;
    int max_extended_width = DEFAULT_MAX_EXTENDED_WIDTH;
    int periods[MAX_PERIOD_TRIALS] = {1};
    int period_count = 1;
    bool try_both_dx = false;
    if (!parse_int_arg(argv[2], "width", &width)
        || !parse_int_arg(argv[3], "period_t", &steps)
        || !parse_int_arg(argv[4], "period_x", &dx)) {
        return 2;
    }
    for (int arg = 5; arg < argc; arg++) {
        if (strcmp(argv[arg], "--max-extended-width") == 0 || strcmp(argv[arg], "--extended-width") == 0) {
            if (arg + 1 >= argc || !parse_int_arg(argv[arg + 1], "max_extended_width", &max_extended_width)) {
                usage(argv[0]);
                return 2;
            }
            arg++;
        } else if (strcmp(argv[arg], "--try-periods") == 0) {
            if (arg + 1 >= argc || !parse_period_list(argv[arg + 1], periods, &period_count)) {
                usage(argv[0]);
                return 2;
            }
            arg++;
        } else if (strcmp(argv[arg], "--try-both-dx") == 0) {
            try_both_dx = true;
        } else {
            usage(argv[0]);
            return 2;
        }
    }
    if (width <= 0 || width > MAX_SEED_WIDTH || steps < 0 || max_extended_width < 0
        || max_extended_width > HARD_MAX_EXTENDED_WIDTH
        || width + max_extended_width > MAX_SEED_WIDTH) {
        fprintf(stderr,
                "invalid search bounds: width must stay in 1..%d, max extended width must stay in 0..%d, and period_t must be nonnegative\n",
                MAX_SEED_WIDTH,
                HARD_MAX_EXTENDED_WIDTH);
        return 2;
    }

    unsigned long found = 0;
    unsigned long exact_found = 0;
    struct Candidate best = {0};
    struct Work work = {0};
    printf("# glider=%s width=%d max_extended_width=%d period=(%d,%d) side_ether_periods=%d multiperiod=%d try_periods=",
           name,
           width,
           max_extended_width,
           steps,
           dx,
           SIDE_ETHER_PERIODS,
           MULTIPERIOD_CHECKS);
    for (int i = 0; i < period_count; i++) {
        printf("%s%d", i == 0 ? "" : ",", periods[i]);
    }
    printf(" try_both_dx=%s\n", try_both_dx ? "yes" : "no");

    for (int seed_width = width; seed_width <= width + max_extended_width; seed_width++) {
        uint64_t limit = UINT64_C(1) << (unsigned)seed_width;
        for (uint64_t seed = 0; seed < limit; seed++) {
            for (int phase = 0; phase < ETHER_PERIOD; phase++) {
                for (int period_index = 0; period_index < period_count; period_index++) {
                    int period_multiplier = periods[period_index];
                    int dx_variants[2] = {dx, -dx};
                    int dx_count = try_both_dx && dx != 0 ? 2 : 1;
                    for (int dx_index = 0; dx_index < dx_count; dx_index++) {
                        int period_steps = steps * period_multiplier;
                        int period_dx = dx_variants[dx_index] * period_multiplier;
                        struct Candidate candidate = {0};
                        if (!verify_seed(seed,
                                         seed_width,
                                         period_steps,
                                         period_dx,
                                         period_multiplier,
                                         phase,
                                         &work,
                                         &candidate)) {
                            continue;
                        }
                        found++;
                        if (candidate.exact) {
                            exact_found++;
                        }
                        printf("%s %d %d %d ", name, seed_width, period_steps, period_dx);
                        print_seed(seed, seed_width);
                        printf(" phase=%d k=%d class=%s exact_kind=%s diff_count=%d diff_span=%d\n",
                               phase,
                               period_multiplier,
                               candidate.exact ? "exact" : "window",
                               candidate.tube_exact ? "tube" : (candidate.exact ? "mask" : "none"),
                               candidate.diff_count,
                               candidate.diff_span);
                        if (better_candidate(candidate, best)) {
                            best = candidate;
                        }
                    }
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
        printf("# best %s width=%d seed=%s phase=%d period=(%d,%d) k=%d class=%s exact_kind=%s diff_count=%d diff_span=%d\n",
               name,
               best.width,
               seed_text,
               best.phase,
               best.period_steps,
               best.period_dx,
               best.period_multiplier,
               best.exact ? "exact" : "window",
               best.tube_exact ? "tube" : (best.exact ? "mask" : "none"),
               best.diff_count,
               best.diff_span);
    }
    return found == 0 ? 1 : 0;
}
