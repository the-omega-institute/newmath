#ifndef COOK_COLLISION_IDENTITY_H
#define COOK_COLLISION_IDENTITY_H

#include <stddef.h>

#define COOK_FIGURE_5_MODULUS 4

typedef enum {
    COLLISION_FIG5A = 0,
    COLLISION_FIG5B = 1,
    COLLISION_FIG5C = 2
} CollisionIdentity;

typedef struct {
    const char *input_left;
    const char *input_right;
    int input_offset;
    const char *output_left;
    const char *output_right;
    int output_offset;
    int k;
} CollisionIdentityRow;

typedef enum {
    COOK_FIGURE10_FIRST_MOVING_AFTER_INVISIBLE = 0,
    COOK_FIGURE10_INVISIBLE = 1,
    COOK_FIGURE10_MOVING_AFTER_MOVING = 2
} CookFigure10Case;

typedef struct {
    CookFigure10Case which;
    CollisionIdentity primary;
    CollisionIdentity secondary;
    int labels[3];
    size_t label_count;
    int ebar_spacing;
    int c2_spacing;
    int regenerated_c2_from_ebar;
} CookFigure10PassThrough;

const CollisionIdentityRow *cook_figure_5(CollisionIdentity which);
int cook_figure_5_normalize(int value);
int cook_figure_5_accepts_spacing(CollisionIdentity which, int spacing);
int cook_figure_5_output_offset(CollisionIdentity which, int *offset_out);

const CookFigure10PassThrough *cook_figure_10_pass_through(
    CookFigure10Case which);
int cook_figure_10_accepts_c2_spacing(CookFigure10Case which, int spacing);
int cook_figure_10_accepts_ebar_spacing(CookFigure10Case which, int spacing);
int cook_figure_10_regenerated_c2_offset(CookFigure10Case which,
                                         int *offset_out);

#endif
