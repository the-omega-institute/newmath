#ifndef COOK_BLOCKS_H
#define COOK_BLOCKS_H

#include <stddef.h>

typedef enum {
    COOK_BLOCK_A = 0,
    COOK_BLOCK_B,
    COOK_BLOCK_C,
    COOK_BLOCK_D,
    COOK_BLOCK_E,
    COOK_BLOCK_F,
    COOK_BLOCK_G,
    COOK_BLOCK_H,
    COOK_BLOCK_I,
    COOK_BLOCK_J,
    COOK_BLOCK_K,
    COOK_BLOCK_L,
    COOK_BLOCK_COUNT
} CookBlockId;

typedef struct {
    CookBlockId id;
    char symbol;
    const char *name;
    size_t period;
    const char *role;
} CookBlockInfo;

const CookBlockInfo *cook_block_table(size_t *count_out);
const CookBlockInfo *cook_block_by_symbol(char symbol);

#endif
