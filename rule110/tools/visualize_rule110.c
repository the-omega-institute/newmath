#include "cook_detect.h"
#include "cook_encode.h"
#include "glider_phases.h"
#include "rule110.h"

#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>

#define ARRAY_LEN(a) (sizeof(a) / sizeof((a)[0]))

typedef struct {
    const char *name;
    const char *neighbor;
    int period;
    int displacement;
} GliderVizSpec;

typedef struct {
    size_t start;
    size_t end;
    const char *label;
} PacketSlice;

static void die(const char *msg) {
    fprintf(stderr, "visualize_rule110: %s\n", msg);
    exit(1);
}

static void *xmalloc(size_t n) {
    void *p = malloc(n == 0 ? 1 : n);
    if (p == NULL) die("out of memory");
    return p;
}

static void fill_ether(uint8_t *cells, size_t len) {
    size_t ether_len = 0;
    const char *ether = glider_phase("ether", NULL, 1, &ether_len);

    if (ether == NULL || ether_len == 0) die("missing ether phase");
    for (size_t i = 0; i < len; i++) {
        cells[i] = (uint8_t)(ether[i % ether_len] == '1');
    }
}

static void emit_phase_at(uint8_t *cells,
                          size_t len,
                          size_t pos,
                          const char *name,
                          const char *neighbor) {
    size_t phase_len = 0;
    const char *bits = glider_phase(name, neighbor, 1, &phase_len);

    if (bits == NULL) die("missing glider phase");
    if (pos > len || phase_len > len - pos) die("glider outside row");
    for (size_t i = 0; i < phase_len; i++) {
        cells[pos + i] = (uint8_t)(bits[i] == '1');
    }
}

static void svg_begin(double width, double height, const char *title) {
    printf("<svg xmlns=\"http://www.w3.org/2000/svg\" viewBox=\"0 0 %.2f %.2f\" width=\"%.0f\" height=\"%.0f\" role=\"img\">\n",
           width,
           height,
           width,
           height);
    printf("<title>%s</title>\n", title);
    printf("<rect x=\"0\" y=\"0\" width=\"%.2f\" height=\"%.2f\" fill=\"#f7f7f4\"/>\n",
           width,
           height);
    printf("<style>text{font-family:Arial,Helvetica,sans-serif;fill:#222}.small{font-size:11px;fill:#555}.axis{font-size:10px;fill:#666}.pix{fill:none;stroke:#111;stroke-width:1;shape-rendering:crispEdges}.mark{stroke:#c0392b;stroke-width:1.2;stroke-dasharray:4 3}.slice{stroke:#2c3e50;stroke-width:1;stroke-dasharray:3 3}</style>\n");
}

static void svg_end(void) {
    printf("</svg>\n");
}

static void text_at(double x, double y, int size, const char *weight, const char *text) {
    printf("<text x=\"%.2f\" y=\"%.2f\" font-size=\"%d\" font-weight=\"%s\">%s</text>\n",
           x,
           y,
           size,
           weight,
           text);
}

static void panel_background(double x,
                             double y,
                             double width,
                             double height,
                             const char *fill) {
    printf("<rect x=\"%.2f\" y=\"%.2f\" width=\"%.2f\" height=\"%.2f\" fill=\"%s\" stroke=\"#cfcfc8\" stroke-width=\"1\"/>\n",
           x,
           y,
           width,
           height,
           fill);
}

static void emit_black_run_path_segments(const uint8_t *row, size_t len, size_t y) {
    size_t x = 0;

    while (x < len) {
        while (x < len && row[x] == 0) x++;
        if (x < len) {
            size_t start = x;
            while (x < len && row[x] != 0) x++;
            printf("M%zu %zu h%zu ", start, y, x - start);
        }
    }
}

static void emit_spacetime_group(uint8_t *cells,
                                 size_t width,
                                 size_t steps,
                                 double x,
                                 double y,
                                 double cell_w,
                                 double cell_h) {
    printf("<g transform=\"translate(%.2f %.2f) scale(%.5f %.5f)\" fill=\"#111\">\n",
           x,
           y,
           cell_w,
           cell_h);
    printf("<path class=\"pix\" d=\"");
    for (size_t t = 0; t < steps; t++) {
        emit_black_run_path_segments(cells, width, t);
        if (t + 1 < steps) r110_run_n_steps(cells, width, 1);
    }
    printf("\"/>\n</g>\n");
}

static void emit_downsampled_group(uint8_t *cells,
                                   size_t width,
                                   size_t steps,
                                   size_t out_w,
                                   size_t out_h,
                                   double x,
                                   double y,
                                   double plot_w,
                                   double plot_h) {
    size_t *acc = (size_t *)xmalloc(out_w * sizeof(*acc));
    uint8_t *row = (uint8_t *)xmalloc(out_w);
    size_t t = 0;

    printf("<g transform=\"translate(%.2f %.2f) scale(%.5f %.5f)\" fill=\"#111\">\n",
           x,
           y,
           plot_w / (double)out_w,
           plot_h / (double)out_h);
    printf("<path class=\"pix\" d=\"");

    for (size_t oy = 0; oy < out_h; oy++) {
        size_t start_t = (oy * steps) / out_h;
        size_t end_t = ((oy + 1u) * steps) / out_h;
        size_t row_count = end_t > start_t ? end_t - start_t : 1u;

        while (t < start_t) {
            r110_run_n_steps(cells, width, 1);
            t++;
        }

        memset(acc, 0, out_w * sizeof(*acc));
        for (; t < end_t; t++) {
            for (size_t ox = 0; ox < out_w; ox++) {
                size_t sx0 = (ox * width) / out_w;
                size_t sx1 = ((ox + 1u) * width) / out_w;
                if (sx1 <= sx0) sx1 = sx0 + 1u;
                if (sx1 > width) sx1 = width;
                for (size_t sx = sx0; sx < sx1; sx++) {
                    acc[ox] += cells[sx] ? 1u : 0u;
                }
            }
            if (t + 1u < steps) r110_run_n_steps(cells, width, 1);
        }

        for (size_t ox = 0; ox < out_w; ox++) {
            size_t sx0 = (ox * width) / out_w;
            size_t sx1 = ((ox + 1u) * width) / out_w;
            size_t bin_w = sx1 > sx0 ? sx1 - sx0 : 1u;
            size_t total = bin_w * row_count;
            row[ox] = (uint8_t)(acc[ox] * 2u >= total);
        }
        emit_black_run_path_segments(row, out_w, oy);
    }
    printf("\"/>\n</g>\n");

    free(row);
    free(acc);
}

static void emit_initial_strip(const uint8_t *cells,
                               size_t width,
                               size_t out_w,
                               double x,
                               double y,
                               double plot_w,
                               double plot_h) {
    uint8_t *row = (uint8_t *)xmalloc(out_w);

    for (size_t ox = 0; ox < out_w; ox++) {
        size_t sx0 = (ox * width) / out_w;
        size_t sx1 = ((ox + 1u) * width) / out_w;
        size_t ones = 0;
        size_t total = 0;

        if (sx1 <= sx0) sx1 = sx0 + 1u;
        if (sx1 > width) sx1 = width;
        for (size_t sx = sx0; sx < sx1; sx++) {
            ones += cells[sx] ? 1u : 0u;
            total++;
        }
        row[ox] = (uint8_t)(ones * 2u >= total);
    }

    panel_background(x, y, plot_w, plot_h, "#fff");
    printf("<g transform=\"translate(%.2f %.2f) scale(%.5f %.5f)\" fill=\"#111\">\n",
           x,
           y,
           plot_w / (double)out_w,
           plot_h);
    printf("<path class=\"pix\" d=\"");
    emit_black_run_path_segments(row, out_w, 0);
    printf("\"/>\n</g>\n");

    free(row);
}

static void emit_axis_labels(double x, double y, double width, double height) {
    printf("<text class=\"axis\" x=\"%.2f\" y=\"%.2f\">cell position</text>\n",
           x + width - 66.0,
           y + height + 15.0);
    printf("<text class=\"axis\" x=\"%.2f\" y=\"%.2f\" transform=\"rotate(90 %.2f %.2f)\">time step</text>\n",
           x - 24.0,
           y + 10.0,
           x - 24.0,
           y + 10.0);
}

static void render_ether(void) {
    enum { W = 140, T = 70 };
    uint8_t cells[W];
    double plot_x = 32.0;
    double plot_y = 42.0;
    double cell_w = 3.0;
    double cell_h = 3.0;

    fill_ether(cells, W);
    svg_begin(486.0, 300.0, "Pure ether: period 7, displacement 0");
    text_at(24.0, 26.0, 18, "700", "Pure ether: period 7, displacement 0");
    panel_background(plot_x, plot_y, W * cell_w, T * cell_h, "#fff");
    emit_spacetime_group(cells, W, T, plot_x, plot_y, cell_w, cell_h);
    emit_axis_labels(plot_x, plot_y, W * cell_w, T * cell_h);
    text_at(32.0, 282.0, 11, "400", "Initial row repeats 11111000100110 across 140 cells; black cells are 1.");
    svg_end();
}

static void render_glider_zoo(void) {
    static const GliderVizSpec specs[] = {
        {"A", NULL, 3, 2},
        {"B", NULL, 4, -2},
        {"C1", "A", 7, 0},
        {"Ebar", "A", 30, -8},
        {"F", "A", 36, -4},
        {"G", "A", 42, -14}
    };
    enum { W = 140 };
    const double panel_w = 320.0;
    const double panel_h = 196.0;
    const double plot_w = 280.0;
    const double plot_h = 142.0;
    const double margin_x = 24.0;
    const double margin_y = 44.0;
    const double gap_x = 20.0;
    const double gap_y = 22.0;

    svg_begin(704.0, 674.0, "Rule 110 glider catalog");
    text_at(24.0, 27.0, 18, "700", "Rule 110 particle catalog on ether");

    for (size_t i = 0; i < ARRAY_LEN(specs); i++) {
        uint8_t cells[W];
        size_t phase_len = 0;
        const char *phase = glider_phase(specs[i].name,
                                         specs[i].neighbor,
                                         1,
                                         &phase_len);
        size_t steps = (size_t)specs[i].period * 3u;
        size_t col = i % 2u;
        size_t row = i / 2u;
        double px = margin_x + (double)col * (panel_w + gap_x);
        double py = margin_y + (double)row * (panel_h + gap_y);
        double gx = px + 20.0;
        double gy = py + 36.0;
        char label[96];

        if (phase == NULL || phase_len > W) die("missing zoo phase");
        fill_ether(cells, W);
        emit_phase_at(cells,
                      W,
                      (W - phase_len) / 2u,
                      specs[i].name,
                      specs[i].neighbor);
        snprintf(label,
                 sizeof(label),
                 "%s phase 0: period %d, displacement %d",
                 specs[i].name,
                 specs[i].period,
                 specs[i].displacement);
        panel_background(px, py, panel_w, panel_h, "#fff");
        text_at(px + 14.0, py + 22.0, 13, "700", label);
        emit_spacetime_group(cells,
                             W,
                             steps,
                             gx,
                             gy,
                             plot_w / (double)W,
                             plot_h / (double)steps);
        printf("<rect x=\"%.2f\" y=\"%.2f\" width=\"%.2f\" height=\"%.2f\" fill=\"none\" stroke=\"#d5d5cf\"/>\n",
               gx,
               gy,
               plot_w,
               plot_h);
        printf("<text class=\"small\" x=\"%.2f\" y=\"%.2f\">T=%zu</text>\n",
               gx + plot_w - 34.0,
               gy + plot_h + 16.0,
               steps);
    }
    svg_end();
}

static void render_collision(void) {
    enum { W = 360, T = 220 };
    uint8_t cells[W];
    uint8_t final_row[W];
    GliderHit hits[96];
    const size_t pos_a = 130;
    const size_t pos_ebar = pos_a + 6u + (4u * 14u) - 51u;
    const double plot_x = 34.0;
    const double plot_y = 44.0;
    const double cell_w = 2.5;
    const double cell_h = 1.78;
    int hit_count = 0;

    fill_ether(cells, W);
    emit_phase_at(cells, W, pos_a, "A", NULL);
    emit_phase_at(cells, W, pos_ebar, "Ebar", "A");

    svg_begin(970.0, 500.0, "A + Ebar(A) &#8594; {Ebar, A}");
    text_at(24.0, 26.0, 18, "700", "A + Ebar(A) &#8594; {Ebar, A}");
    text_at(24.0, 43.0, 11, "400", "Martinez 2012 Table 2 row 8; initial gap 4 ether periods, audit delta -51.");
    panel_background(plot_x, plot_y, W * cell_w, T * cell_h, "#fff");
    emit_spacetime_group(cells, W, T, plot_x, plot_y, cell_w, cell_h);
    memcpy(final_row, cells, sizeof(final_row));
    emit_axis_labels(plot_x, plot_y, W * cell_w, T * cell_h);
    printf("<line class=\"mark\" x1=\"%.2f\" y1=\"%.2f\" x2=\"%.2f\" y2=\"%.2f\"/>\n",
           plot_x,
           plot_y + 120.0 * cell_h,
           plot_x + W * cell_w,
           plot_y + 120.0 * cell_h);
    text_at(plot_x + 8.0, plot_y + 120.0 * cell_h - 5.0, 11, "700", "collision window t=120");

    hit_count = cook_detect_gliders(final_row,
                                    W,
                                    184,
                                    hits,
                                    ARRAY_LEN(hits));
    if (hit_count > 0) {
        int marked_a = 0;
        int marked_e = 0;

        for (int i = 0; i < hit_count; i++) {
            const char *label = NULL;
            if (!marked_e && strcmp(hits[i].name, "Ebar") == 0) {
                label = "detected Ebar outcome";
                marked_e = 1;
            } else if (!marked_a && strcmp(hits[i].name, "A") == 0) {
                label = "detected A outcome";
                marked_a = 1;
            }
            if (label != NULL) {
                double x = plot_x + (double)hits[i].initial_position * cell_w;
                printf("<line class=\"mark\" x1=\"%.2f\" y1=\"%.2f\" x2=\"%.2f\" y2=\"%.2f\"/>\n",
                       x,
                       plot_y + T * cell_h - 26.0,
                       x,
                       plot_y + T * cell_h);
                text_at(x + 4.0, plot_y + T * cell_h - 31.0, 11, "700", label);
            }
        }
    }

    svg_end();
}

static int phase_exact_core(const CyclicTagInput *ct,
                            size_t start_cap,
                            size_t max_cap,
                            uint8_t **cells_out,
                            size_t *len_out) {
    size_t cap = start_cap;

    while (cap <= max_cap) {
        uint8_t *cells = (uint8_t *)xmalloc(cap);
        size_t written = 0;
        int rc = cook_encode_phase_exact(ct, cells, cap, &written);

        if (rc == COOK_ENCODE_PHASE_EXACT_OK && written > 0 && written < cap) {
            *cells_out = cells;
            *len_out = written;
            return 1;
        }
        free(cells);
        if (cap > max_cap / 2u) break;
        cap *= 2u;
    }
    return 0;
}

static void packet_layout_slices(const CyclicTagInput *ct,
                                 PacketSlice *slices,
                                 size_t *slice_count) {
    size_t ys = 0;
    size_t ns = 0;
    size_t nonempty = 0;
    size_t empty = 0;
    size_t left_v = 0;
    size_t left_slots = 0;
    size_t central_blocks = 0;
    size_t right_blocks = 0;
    size_t left_end = 0;
    size_t central_end = 0;
    size_t right_end = 0;

    for (size_t i = 0; i < ct->num_productions; i++) {
        if (ct->prod_lens[i] == 0) {
            empty++;
        } else {
            nonempty++;
        }
        for (size_t j = 0; j < ct->prod_lens[i]; j++) {
            if (ct->productions[i][j] == 0) ns++;
            else ys++;
        }
        right_blocks += ct->prod_lens[i] == 0 ? 1u : (ct->prod_lens[i] * 2u) + 1u;
    }
    for (size_t i = 0; i < ct->tape_len; i++) {
        if (ct->initial_tape[i] == 0) ns++;
        else ys++;
    }
    left_v = (ys * 76u) + (ns * 80u) + (nonempty * 60u) + (empty * 43u);
    central_blocks = ct->tape_len == 0 ? 2u : (ct->tape_len * 2u) + 1u;
    left_slots = (left_v + 13u + 11u + 12u + 4u) * 3u;

    left_end = (64u * 14u) + (left_slots * 14u);
    central_end = left_end + (central_blocks * 14u);
    right_end = central_end + (right_blocks * 14u);

    slices[0].start = 64u * 14u;
    slices[0].end = left_end;
    slices[0].label = "left periodic A blocks";
    slices[1].start = left_end;
    slices[1].end = central_end;
    slices[1].label = "central C(E/F)D...G";
    slices[2].start = central_end;
    slices[2].end = right_end;
    slices[2].label = "right appendant blocks";
    *slice_count = 3u;
}

static void emit_packet_slice_labels(const PacketSlice *slices,
                                     size_t slice_count,
                                     size_t row_width,
                                     double x,
                                     double y,
                                     double plot_w,
                                     double strip_h) {
    for (size_t i = 0; i < slice_count; i++) {
        double sx = x + ((double)slices[i].start / (double)row_width) * plot_w;
        double ex = x + ((double)slices[i].end / (double)row_width) * plot_w;
        double mid = (sx + ex) / 2.0;

        if (sx < x) sx = x;
        if (ex > x + plot_w) ex = x + plot_w;
        printf("<line class=\"slice\" x1=\"%.2f\" y1=\"%.2f\" x2=\"%.2f\" y2=\"%.2f\"/>\n",
               sx,
               y - 4.0,
               sx,
               y + strip_h + 8.0);
        printf("<line class=\"slice\" x1=\"%.2f\" y1=\"%.2f\" x2=\"%.2f\" y2=\"%.2f\"/>\n",
               ex,
               y - 4.0,
               ex,
               y + strip_h + 8.0);
        printf("<text class=\"small\" text-anchor=\"middle\" x=\"%.2f\" y=\"%.2f\">%s</text>\n",
               mid,
               y - 9.0,
               slices[i].label);
    }
}

static void render_cook_packet(void) {
    uint8_t prod0[2] = {1, 0};
    uint8_t prod1[1] = {1};
    uint8_t *productions[2] = {prod0, prod1};
    size_t prod_lens[2] = {2, 1};
    uint8_t tape[2] = {1, 0};
    CyclicTagInput ct = {productions, prod_lens, 2, tape, 2};
    uint8_t *cells = NULL;
    uint8_t *evolve = NULL;
    size_t len = 0;
    PacketSlice slices[3];
    size_t slice_count = 0;
    const double plot_x = 34.0;
    const double strip_y = 74.0;
    const double plot_y = 126.0;
    const double plot_w = 900.0;
    const double plot_h = 430.0;
    const size_t out_w = 720;
    const size_t out_h = 344;

    if (!phase_exact_core(&ct, 65536u, 1048576u, &cells, &len)) {
        die("could not encode Cook packet");
    }
    evolve = (uint8_t *)xmalloc(len);
    memcpy(evolve, cells, len);
    packet_layout_slices(&ct, slices, &slice_count);

    svg_begin(970.0,
              610.0,
              "Cook 2009 &#167;1.4: 2 production x 2 tape bit packet, 2048 step evolution");
    text_at(24.0,
            28.0,
            18,
            "700",
            "Cook 2009 &#167;1.4: 2 production x 2 tape bit packet, 2048 step evolution");
    text_at(24.0,
            49.0,
            11,
            "400",
            "Top strip is the encoded initial row; the large panel is a majority-downsampled space-time diagram.");
    emit_initial_strip(cells, len, out_w, plot_x, strip_y, plot_w, 18.0);
    emit_packet_slice_labels(slices, slice_count, len, plot_x, strip_y, plot_w, 18.0);
    panel_background(plot_x, plot_y, plot_w, plot_h, "#fff");
    emit_downsampled_group(evolve,
                           len,
                           2048u,
                           out_w,
                           out_h,
                           plot_x,
                           plot_y,
                           plot_w,
                           plot_h);
    emit_axis_labels(plot_x, plot_y, plot_w, plot_h);
    svg_end();

    free(evolve);
    free(cells);
}

static void render_scale(void) {
    uint8_t prod0[2] = {1, 0};
    uint8_t prod1[2] = {0, 1};
    uint8_t *productions[2] = {prod0, prod1};
    size_t prod_lens[2] = {2, 2};
    uint8_t tape[16] = {
        1, 0, 0, 1, 0, 1, 0, 0,
        1, 0, 0, 0, 1, 0, 1, 0
    };
    CyclicTagInput ct = {productions, prod_lens, 2, tape, 16};
    uint8_t *cells = NULL;
    uint8_t *evolve = NULL;
    size_t len = 0;
    const double plot_x = 34.0;
    const double strip_y = 70.0;
    const double plot_y = 112.0;
    const double plot_w = 420.0;
    const double plot_h = 420.0;
    const size_t out_w = 280;
    const size_t out_h = 280;

    if (!phase_exact_core(&ct, 65536u, 2097152u, &cells, &len)) {
        die("could not encode scale frontier");
    }
    evolve = (uint8_t *)xmalloc(len);
    memcpy(evolve, cells, len);

    svg_begin(490.0,
              590.0,
              "Cook packet scale frontier: 2 production x 16 tape bit x 16384 steps");
    text_at(24.0,
            28.0,
            18,
            "700",
            "Cook packet scale frontier: 2 production x 16 tape bit x 16384 steps");
    text_at(24.0,
            49.0,
            11,
            "400",
            "The 16384-step run is majority-downsampled to a compact viewport.");
    emit_initial_strip(cells, len, out_w, plot_x, strip_y, plot_w, 16.0);
    panel_background(plot_x, plot_y, plot_w, plot_h, "#fff");
    emit_downsampled_group(evolve,
                           len,
                           16384u,
                           out_w,
                           out_h,
                           plot_x,
                           plot_y,
                           plot_w,
                           plot_h);
    emit_axis_labels(plot_x, plot_y, plot_w, plot_h);
    svg_end();

    free(evolve);
    free(cells);
}

int main(int argc, char **argv) {
    if (argc != 2) {
        fprintf(stderr,
                "usage: %s ether|glider_zoo|collision|cook_packet|scale\n",
                argv[0]);
        return 1;
    }

    if (strcmp(argv[1], "ether") == 0) {
        render_ether();
    } else if (strcmp(argv[1], "glider_zoo") == 0) {
        render_glider_zoo();
    } else if (strcmp(argv[1], "collision") == 0) {
        render_collision();
    } else if (strcmp(argv[1], "cook_packet") == 0) {
        render_cook_packet();
    } else if (strcmp(argv[1], "scale") == 0) {
        render_scale();
    } else {
        fprintf(stderr, "unknown visualization: %s\n", argv[1]);
        return 1;
    }

    return 0;
}
