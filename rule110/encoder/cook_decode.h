#ifndef COOK_DECODE_H
#define COOK_DECODE_H

#include <stddef.h>
#include <stdint.h>

#define COOK_DECODE_OK 0
#define COOK_DECODE_INVALID_INPUT 1
#define COOK_DECODE_NO_OUTPUT 2
#define COOK_DECODE_OUTPUT_TRUNCATED 3

int cook_decode_output(const uint8_t *evolved_row,
                       size_t len,
                       char *out_buf,
                       size_t buf_size);

#endif
