#include "cook_glider_gun.h"
#include <string.h>

const size_t COOK_GLIDER_GUN_WIDTH = 518;
const size_t COOK_GLIDER_GUN_EMISSION_PERIOD = 168;

void cook_glider_gun_emit(uint8_t *out, size_t pos, size_t buf_len) {
    static const uint8_t GUN_E[6] = {1, 1, 1, 0, 0, 1};
    static const uint8_t GUN_F[7] = {1, 1, 0, 0, 1, 0, 1};
    static const uint8_t GUN_G[12] =
        {1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 1};
    static const uint8_t GUN_H[14] =
        {1, 0, 1, 1, 0, 1, 0, 0, 1, 0, 1, 1, 1, 0};

    /*
       Cook 2004 uses repeating ether-localized particle sources in the
       cyclic tag construction. This source band places separated E/F/G/H
       row approximations at a 168-cell phase spacing, producing multiple
       mobile perturbations under direct Rule 110 evolution.
    */
    if (pos > buf_len || COOK_GLIDER_GUN_WIDTH > buf_len - pos) return;

    memcpy(out + pos, GUN_E, sizeof(GUN_E));
    memcpy(out + pos + COOK_GLIDER_GUN_EMISSION_PERIOD, GUN_F, sizeof(GUN_F));
    memcpy(out + pos + (2 * COOK_GLIDER_GUN_EMISSION_PERIOD),
           GUN_G,
           sizeof(GUN_G));
    memcpy(out + pos + (3 * COOK_GLIDER_GUN_EMISSION_PERIOD),
           GUN_H,
           sizeof(GUN_H));
}
