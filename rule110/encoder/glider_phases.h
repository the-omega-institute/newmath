#ifndef GLIDER_PHASES_H
#define GLIDER_PHASES_H

#include <stddef.h>
#include <stdint.h>

const char *glider_phase(const char *glider_name,
                         const char *neighbor,
                         int phase,
                         size_t *out_len);

int glider_phase_emit(uint8_t *out,
                      size_t pos,
                      size_t buf_len,
                      const char *glider_name,
                      const char *neighbor,
                      int phase,
                      size_t *written_out);

extern const char COOK_ETHER_PATTERN_STR[];

#endif
