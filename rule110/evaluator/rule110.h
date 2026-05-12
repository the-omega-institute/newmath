#ifndef RULE110_H
#define RULE110_H

#include <stdio.h>
#include <stdint.h>
#include <stddef.h>

/* In-place one step of Rule 110 cellular automaton with fixed boundary (off-grid cells = 0). */
void r110_step(uint8_t *cells, size_t len);

/* In-place n steps. */
void r110_run_n_steps(uint8_t *cells, size_t len, size_t n);

/* Write cells as '0'/'1' followed by '\n' to out. */
void r110_dump_state(const uint8_t *cells, size_t len, FILE *out);

#endif
