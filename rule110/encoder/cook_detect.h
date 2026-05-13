#ifndef COOK_DETECT_H
#define COOK_DETECT_H

#include <stddef.h>
#include <stdint.h>

typedef struct {
    const char *name;
    const char *neighbor;
    int phase;
    int displacement;
    size_t initial_position;
    size_t final_position;
} GliderHit;

int cook_detect_gliders(const uint8_t *initial_row,
                        size_t initial_len,
                        size_t total_steps,
                        GliderHit *hits_out,
                        size_t hits_cap);

#endif
