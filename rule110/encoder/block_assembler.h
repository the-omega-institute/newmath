#ifndef BLOCK_ASSEMBLER_H
#define BLOCK_ASSEMBLER_H

#include <stddef.h>
#include <stdint.h>
#include <stdio.h>

typedef struct {
    size_t ys;
    size_t ns;
    size_t nonempty;
    size_t empty;
} CookAppenderStats;

typedef struct {
    char *data;
    size_t len;
    size_t cap;
    size_t count;
} CookBlockString;

void cook_block_string_init(CookBlockString *s);
void cook_block_string_free(CookBlockString *s);
int cook_block_string_append(CookBlockString *s, char symbol);

int cook_count_appendants(const uint8_t *const *productions,
                          const size_t *prod_lens,
                          size_t production_count,
                          CookAppenderStats *out);
size_t cook_left_v_from_stats(const CookAppenderStats *stats);
int cook_write_left_periodic(FILE *out, size_t left_v);

int cook_assemble_central_from_bits(const uint8_t *bits,
                                    size_t bits_len,
                                    CookBlockString *out);
int cook_assemble_right(const uint8_t *const *productions,
                        const size_t *prod_lens,
                        size_t production_count,
                        CookBlockString *out);
int cook_central_bits_from_blocks(const CookBlockString *blocks,
                                  char **bits_out,
                                  size_t *bits_len_out);
int cook_scan_appendants_file(const char *path,
                              CookAppenderStats *stats,
                              CookBlockString *right);
int cook_validate_symbolic_case(const char *input,
                                const char *left_blocks,
                                size_t left_v,
                                size_t expected_left_v,
                                const char *central_blocks,
                                const char *central_bits,
                                const char *right_blocks,
                                size_t right_count,
                                const CookBlockString *expected_right);
int cook_read_validate_symbolic_case(FILE *f,
                                     const char *case_line,
                                     size_t expected_left_v,
                                     const CookBlockString *expected_right);
int cook_source_binary_direct_count(const char *path,
                                    size_t *count_out);
int cook_source_case_input_matches(const char *path,
                                   const char *name,
                                   const char *input);

#endif
