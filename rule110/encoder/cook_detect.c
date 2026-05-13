#include "cook_detect.h"

#include "glider_phases.h"
#include "rule110.h"

#include <stdlib.h>
#include <string.h>

typedef struct {
    const char *name;
    int period;
    int displacement;
} GliderMotion;

static const GliderMotion GLIDER_MOTIONS[] = {
    {"A", 3, 2},
    {"B", 4, -2},
    {"Bbar", 12, -6},
    {"Bhat", 12, -6},
    {"C1", 7, 0},
    {"C2", 7, 0},
    {"C3", 7, 0},
    {"D1", 10, 2},
    {"D2", 10, 2},
    {"E", 15, -4},
    {"Ebar", 30, -8},
    {"F", 36, -4},
    {"G", 42, -14},
    {"H", 92, -18},
    {"Gun", 77, -20}
};

typedef struct {
    const char *name;
    const char *neighbors[12];
} PhaseScanSpec;

static const PhaseScanSpec PHASE_SCAN_SPECS[] = {
    {"Bbar", {"A", "B", "C", NULL}},
    {"C1", {"A", "B", NULL}},
    {"C2", {"A", "B", NULL}},
    {"C3", {"A", "B", NULL}},
    {"G", {"A", "B", "C", "D", "E", "F", "G", "H", "A2", "B2", "C2", NULL}}
};

typedef struct {
    const GliderMotion *motion;
    const char *neighbor;
    int phase;
    const char *bits;
    size_t len;
} PhasePattern;

static void diff_against_ether(const uint8_t *evolved,
                               const uint8_t *ether,
                               size_t len,
                               uint8_t *diff_out) {
    for (size_t i = 0; i < len; i++) {
        diff_out[i] = (uint8_t)(evolved[i] != ether[i]);
    }
}

static size_t find_glider_runs(const uint8_t *diff,
                               size_t len,
                               size_t *run_starts,
                               size_t *run_lens,
                               size_t runs_cap) {
    enum { QUIET_BRIDGE = 3 };
    size_t count = 0;
    size_t pos = 0;

    while (pos < len) {
        size_t start = 0;
        size_t last_active = 0;
        size_t run_len = 0;
        size_t quiet = 0;

        while (pos < len && diff[pos] == 0) pos++;
        if (pos >= len) break;
        start = pos;
        last_active = pos;
        while (pos < len) {
            if (diff[pos] != 0) {
                last_active = pos;
                quiet = 0;
            } else {
                quiet++;
                if (quiet > (size_t)QUIET_BRIDGE) break;
            }
            pos++;
        }
        run_len = last_active + 1u - start;
        if (count < runs_cap) {
            run_starts[count] = start;
            run_lens[count] = run_len;
        }
        count++;
    }
    return count > runs_cap ? runs_cap : count;
}

static void fill_best_ether(const uint8_t *row, size_t len, uint8_t *ether) {
    size_t ether_len = 0;
    const char *bits = glider_phase("ether", NULL, 1, &ether_len);
    size_t best_phase = 0;
    size_t best_score = 0;

    if (bits == NULL || ether_len == 0) abort();
    for (size_t phase = 0; phase < ether_len; phase++) {
        size_t score = 0;

        for (size_t i = 0; i < len; i++) {
            if ((row[i] ? 1 : 0) == (bits[(i + phase) % ether_len] == '1' ? 1 : 0)) {
                score++;
            }
        }
        if (score > best_score) {
            best_score = score;
            best_phase = phase;
        }
    }
    for (size_t i = 0; i < len; i++) {
        ether[i] = (uint8_t)(bits[(i + best_phase) % ether_len] == '1');
    }
}

static int same_hit(const GliderHit *hit,
                    const char *name,
                    const char *neighbor,
                    int phase,
                    size_t initial_position,
                    size_t final_position) {
    if (hit->name != name) return 0;
    if (hit->neighbor != neighbor) return 0;
    (void)phase;
    (void)initial_position;
    (void)final_position;
    return 1;
}

static int hit_already_recorded(const GliderHit *hits,
                                size_t hit_count,
                                const char *name,
                                const char *neighbor,
                                int phase,
                                size_t initial_position,
                                size_t final_position) {
    for (size_t i = 0; i < hit_count; i++) {
        if (same_hit(&hits[i],
                     name,
                     neighbor,
                     phase,
                     initial_position,
                     final_position)) {
            return 1;
        }
    }
    return 0;
}

static int diff_window_repeats(const uint8_t *diffs,
                               size_t len,
                               size_t t,
                               size_t total_steps,
                               size_t run_start,
                               size_t run_len,
                               const GliderMotion *motion,
                               size_t *final_pos_out) {
    enum { PAD = 6 };
    size_t checks = 0;
    size_t active = 0;
    size_t start = run_start > (size_t)PAD ? run_start - (size_t)PAD : 0u;
    size_t end = run_start + run_len;

    if ((size_t)PAD < len - end) end += (size_t)PAD;
    else end = len;
    for (size_t i = run_start; i < run_start + run_len; i++) {
        if (diffs[(t * len) + i] != 0) active++;
    }
    if (active < 3u) return 0;
    for (size_t step = 1u;
         t + (step * (size_t)motion->period) <= total_steps;
         step++) {
        long dx = (long)motion->displacement * (long)step;
        size_t target_t = t + (step * (size_t)motion->period);

        for (size_t i = start; i < end; i++) {
            long target = (long)i + dx;

            if (target < 0 || target >= (long)len) return 0;
            if (diffs[(t * len) + i] !=
                diffs[(target_t * len) + (size_t)target]) {
                return 0;
            }
        }
        checks++;
        if (checks == 2u) break;
    }
    if (checks < 2u) return 0;
    if (final_pos_out != NULL) {
        long final_pos = (long)run_start +
            ((long)motion->displacement * (long)checks);

        if (final_pos < 0 || final_pos >= (long)len) return 0;
        *final_pos_out = (size_t)final_pos;
    }
    return 1;
}

static int phase_window_matches(const uint8_t *rows,
                                const uint8_t *diffs,
                                size_t len,
                                size_t t,
                                size_t pos,
                                const PhasePattern *pattern) {
    size_t row_offset = t * len;
    int has_diff = 0;

    if (pattern == NULL || pattern->bits == NULL || pattern->len == 0u ||
        pos > len || pattern->len > len - pos) {
        return 0;
    }

    for (size_t i = 0; i < pattern->len; i++) {
        if (rows[row_offset + pos + i] !=
            (uint8_t)(pattern->bits[i] == '1')) {
            return 0;
        }
        if (diffs[row_offset + pos + i] != 0) has_diff = 1;
    }
    if (!has_diff) return 0;
    return 1;
}

static void maybe_record_hit(GliderHit *hits_out,
                             size_t hits_cap,
                             size_t *hit_count,
                             const GliderMotion *motion,
                             const char *neighbor,
                             int phase,
                             size_t pos,
                             size_t final_pos) {
    if (*hit_count < hits_cap &&
        !hit_already_recorded(hits_out,
                              *hit_count,
                              motion->name,
                              neighbor,
                              phase,
                              pos,
                              final_pos)) {
        hits_out[*hit_count].name = motion->name;
        hits_out[*hit_count].neighbor = neighbor;
        hits_out[*hit_count].phase = phase - 1;
        hits_out[*hit_count].displacement = motion->displacement;
        hits_out[*hit_count].initial_position = pos;
        hits_out[*hit_count].final_position = final_pos;
        (*hit_count)++;
    } else if (*hit_count >= hits_cap) {
        (*hit_count)++;
    }
}

static int glider_name_recorded(const GliderHit *hits,
                                size_t hit_count,
                                const char *name) {
    for (size_t i = 0; i < hit_count; i++) {
        if (strcmp(hits[i].name, name) == 0) return 1;
    }
    return 0;
}

static size_t collect_phase_patterns(PhasePattern *patterns,
                                     size_t patterns_cap) {
    size_t count = 0;

    for (size_t g = 0;
         g < sizeof(PHASE_SCAN_SPECS) / sizeof(PHASE_SCAN_SPECS[0]);
         g++) {
        const PhaseScanSpec *scan = &PHASE_SCAN_SPECS[g];
        const GliderMotion *motion = NULL;

        for (size_t m = 0;
             m < sizeof(GLIDER_MOTIONS) / sizeof(GLIDER_MOTIONS[0]);
             m++) {
            if (strcmp(GLIDER_MOTIONS[m].name, scan->name) == 0) {
                motion = &GLIDER_MOTIONS[m];
                break;
            }
        }
        if (motion == NULL) continue;
        for (size_t n = 0; scan->neighbors[n] != NULL; n++) {
            for (int phase = 1; phase <= 4; phase++) {
                size_t phase_len = 0;
                const char *bits = glider_phase(motion->name,
                                                scan->neighbors[n],
                                                phase,
                                                &phase_len);

                if (bits == NULL || phase_len == 0u) continue;
                if (count < patterns_cap) {
                    patterns[count].motion = motion;
                    patterns[count].neighbor = scan->neighbors[n];
                    patterns[count].phase = phase;
                    patterns[count].bits = bits;
                    patterns[count].len = phase_len;
                }
                count++;
            }
        }
    }
    return count > patterns_cap ? patterns_cap : count;
}

static void scan_phase_catalog_at_runs(const uint8_t *rows,
                                       const uint8_t *diffs,
                                       size_t len,
                                       size_t t,
                                       const size_t *run_starts,
                                       const size_t *run_lens,
                                       size_t run_count,
                                       GliderHit *hits_out,
                                       size_t hits_cap,
                                       size_t *hit_count,
                                       const PhasePattern *patterns,
                                       size_t pattern_count) {
    enum { PAD = 96 };

    for (size_t run = 0; run < run_count; run++) {
        size_t start = run_starts[run] > (size_t)PAD ?
            run_starts[run] - (size_t)PAD : 0u;
        size_t end = run_starts[run] + run_lens[run] + (size_t)PAD;

        if (end > len) end = len;
        for (size_t p = 0; p < pattern_count; p++) {
            const PhasePattern *pattern = &patterns[p];

            if (pattern->len > len ||
                glider_name_recorded(hits_out,
                                     *hit_count < hits_cap ?
                                     *hit_count : hits_cap,
                                     pattern->motion->name)) {
                continue;
            }
            for (size_t pos = start;
                 pos < end && pos <= len - pattern->len;
                 pos++) {
                if (phase_window_matches(rows,
                                         diffs,
                                         len,
                                         t,
                                         pos,
                                         pattern)) {
                    maybe_record_hit(hits_out,
                                     hits_cap,
                                     hit_count,
                                     pattern->motion,
                                     pattern->neighbor,
                                     pattern->phase,
                                     pos,
                                     pos);
                    break;
                }
            }
        }
    }
}

int cook_detect_gliders(const uint8_t *initial_row,
                        size_t initial_len,
                        size_t total_steps,
                        GliderHit *hits_out,
                        size_t hits_cap) {
    uint8_t *rows = NULL;
    uint8_t *ethers = NULL;
    uint8_t *diffs = NULL;
    size_t *run_starts = NULL;
    size_t *run_lens = NULL;
    PhasePattern phase_patterns[96];
    size_t phase_pattern_count = 0;
    size_t hit_count = 0;

    if (initial_row == NULL || (hits_out == NULL && hits_cap > 0u)) return -1;
    if (initial_len == 0u) return 0;

    rows = (uint8_t *)malloc((total_steps + 1u) * initial_len);
    ethers = (uint8_t *)malloc((total_steps + 1u) * initial_len);
    diffs = (uint8_t *)malloc((total_steps + 1u) * initial_len);
    run_starts = (size_t *)malloc(initial_len * sizeof(*run_starts));
    run_lens = (size_t *)malloc(initial_len * sizeof(*run_lens));
    if (rows == NULL || ethers == NULL || diffs == NULL ||
        run_starts == NULL || run_lens == NULL) {
        free(rows);
        free(ethers);
        free(diffs);
        free(run_starts);
        free(run_lens);
        return -1;
    }

    memcpy(rows, initial_row, initial_len);
    fill_best_ether(initial_row, initial_len, ethers);
    diff_against_ether(rows, ethers, initial_len, diffs);
    phase_pattern_count = collect_phase_patterns(phase_patterns,
                                                 sizeof(phase_patterns) /
                                                 sizeof(phase_patterns[0]));

    for (size_t t = 1; t <= total_steps; t++) {
        memcpy(rows + (t * initial_len),
               rows + ((t - 1u) * initial_len),
               initial_len);
        memcpy(ethers + (t * initial_len),
               ethers + ((t - 1u) * initial_len),
               initial_len);
        r110_step(rows + (t * initial_len), initial_len);
        r110_step(ethers + (t * initial_len), initial_len);
        diff_against_ether(rows + (t * initial_len),
                           ethers + (t * initial_len),
                           initial_len,
                           diffs + (t * initial_len));
    }

    for (size_t t = 0; t <= total_steps; t++) {
        size_t run_count = find_glider_runs(diffs + (t * initial_len),
                                            initial_len,
                                            run_starts,
                                            run_lens,
                                            initial_len);

        scan_phase_catalog_at_runs(rows,
                                   diffs,
                                   initial_len,
                                   t,
                                   run_starts,
                                   run_lens,
                                   run_count,
                                   hits_out,
                                   hits_cap,
                                   &hit_count,
                                   phase_patterns,
                                   phase_pattern_count);
        for (size_t run = 0; run < run_count; run++) {
            for (size_t g = 0;
                 g < sizeof(GLIDER_MOTIONS) / sizeof(GLIDER_MOTIONS[0]);
                 g++) {
                const GliderMotion *motion = &GLIDER_MOTIONS[g];
                size_t final_pos = 0;

                if (t + (2u * (size_t)motion->period) > total_steps) continue;
                if (!diff_window_repeats(diffs,
                                         initial_len,
                                         t,
                                         total_steps,
                                         run_starts[run],
                                         run_lens[run],
                                         motion,
                                         &final_pos)) {
                    continue;
                }
                maybe_record_hit(hits_out,
                                 hits_cap,
                                 &hit_count,
                                 motion,
                                 NULL,
                                 1,
                                 run_starts[run],
                                 final_pos);
            }
        }
    }

    free(rows);
    free(ethers);
    free(diffs);
    free(run_starts);
    free(run_lens);

    if (hit_count > hits_cap) return (int)hits_cap;
    return (int)hit_count;
}
