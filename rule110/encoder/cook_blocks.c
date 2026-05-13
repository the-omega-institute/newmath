#include "cook_blocks.h"

#include <stddef.h>

static const CookBlockInfo COOK_BLOCKS[COOK_BLOCK_COUNT] = {
    {COOK_BLOCK_A, 'A', "ether", 3, "pure ether"},
    {COOK_BLOCK_B, 'B', "ossifier", 0, "A4 ossifier"},
    {COOK_BLOCK_C, 'C', "anchor", 0, "C2 tape anchor"},
    {COOK_BLOCK_D, 'D', "glue", 0, "Ebar glue"},
    {COOK_BLOCK_E, 'E', "data_N", 0, "moving data N"},
    {COOK_BLOCK_F, 'F', "data_Y", 0, "moving data Y"},
    {COOK_BLOCK_G, 'G', "prepared_leader", 0, "prepared leader"},
    {COOK_BLOCK_H, 'H', "primary_component", 0, "primary component"},
    {COOK_BLOCK_I, 'I', "standard_Y", 0, "standard narrow component"},
    {COOK_BLOCK_J, 'J', "standard_N", 0, "standard wide component"},
    {COOK_BLOCK_K, 'K', "raw_leader", 0, "raw leader"},
    {COOK_BLOCK_L, 'L', "raw_short_leader", 0, "raw short leader"},
};

const CookBlockInfo *cook_block_table(size_t *count_out) {
    if (count_out != NULL) *count_out = COOK_BLOCK_COUNT;
    return COOK_BLOCKS;
}

const CookBlockInfo *cook_block_by_symbol(char symbol) {
    size_t i;

    for (i = 0; i < COOK_BLOCK_COUNT; i++) {
        if (COOK_BLOCKS[i].symbol == symbol) return &COOK_BLOCKS[i];
    }
    return NULL;
}
