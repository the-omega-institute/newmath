#ifndef TAG_TO_CYCLIC_H
#define TAG_TO_CYCLIC_H

#include "cook_encode.h"
#include "tm_to_tag.h"

int tag_to_cyclic(const TagSystem *tag,
                  const uint8_t *tag_tape,
                  size_t tag_tape_len,
                  CyclicTagInput *out_cyclic);

void cyclic_tag_input_free(CyclicTagInput *cyclic);

#endif
