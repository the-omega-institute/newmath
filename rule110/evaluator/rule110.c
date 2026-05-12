#include "rule110.h"
#include <stdlib.h>
#include <string.h>

static const uint8_t RULE110_TABLE[8] = {0,1,1,1,0,1,1,0};

void r110_step(uint8_t *cells, size_t len) {
    if (len == 0) return;
    uint8_t *buf = (uint8_t *)malloc(len);
    if (!buf) { perror("malloc"); exit(1); }
    memcpy(buf, cells, len);
    for (size_t i = 0; i < len; i++) {
        uint8_t left  = (i == 0)         ? 0 : buf[i - 1];
        uint8_t self  = buf[i];
        uint8_t right = (i == len - 1)   ? 0 : buf[i + 1];
        cells[i] = RULE110_TABLE[(left << 2) | (self << 1) | right];
    }
    free(buf);
}

void r110_run_n_steps(uint8_t *cells, size_t len, size_t n) {
    for (size_t i = 0; i < n; i++) r110_step(cells, len);
}

void r110_dump_state(const uint8_t *cells, size_t len, FILE *out) {
    for (size_t i = 0; i < len; i++) fputc(cells[i] ? '1' : '0', out);
    fputc('\n', out);
}

#ifdef RULE110_STANDALONE_MAIN
#include <stdio.h>
int main(void) {
    char buf[8192];
    if (!fgets(buf, sizeof(buf), stdin)) {
        fprintf(stderr, "reject: empty_input_policy\n"); return 1;
    }
    size_t bl = strlen(buf);
    if (bl > 0 && buf[bl-1] == '\n') buf[--bl] = 0;
    size_t len = bl;
    if (len == 0) { fprintf(stderr, "reject: empty_input_policy\n"); return 1; }
    uint8_t *cells = (uint8_t *)malloc(len);
    if (!cells) { perror("malloc"); return 1; }
    for (size_t i = 0; i < len; i++) {
        if (buf[i] != '0' && buf[i] != '1') {
            fprintf(stderr, "reject: nonbinary_character at offset %zu\n", i);
            free(cells); return 1;
        }
        cells[i] = (uint8_t)(buf[i] == '1');
    }
    char num_buf[64];
    if (!fgets(num_buf, sizeof(num_buf), stdin)) {
        fprintf(stderr, "reject: missing_step_count\n"); free(cells); return 1;
    }
    size_t n = (size_t)strtoull(num_buf, NULL, 10);
    r110_run_n_steps(cells, len, n);
    r110_dump_state(cells, len, stdout);
    free(cells);
    return 0;
}
#endif
