#include "cook_collision_identity.h"

static const CollisionIdentityRow COOK_FIGURE_5_ROWS[] = {
    {"Ebar", "C2", -1, "Ebar", "C2", 2, 0},
    {"Ebar", "Ebar", 3, "Ebar", "Ebar", 3, 0},
    {"C2", "C2", 2, "C2", "C2", 2, 3}
};

static const CookFigure10PassThrough COOK_FIGURE_10_ROWS[] = {
    {
        COOK_FIGURE10_FIRST_MOVING_AFTER_INVISIBLE,
        COLLISION_FIG5B,
        COLLISION_FIG5A,
        {0, 1, 2},
        3u,
        3,
        2,
        2
    },
    {
        COOK_FIGURE10_INVISIBLE,
        COLLISION_FIG5A,
        COLLISION_FIG5C,
        {2, 1, 0},
        2u,
        -1,
        2,
        2
    },
    {
        COOK_FIGURE10_MOVING_AFTER_MOVING,
        COLLISION_FIG5B,
        COLLISION_FIG5A,
        {0, 1, 2},
        3u,
        3,
        2,
        2
    }
};

const CollisionIdentityRow *cook_figure_5(CollisionIdentity which) {
    if (which < COLLISION_FIG5A || which > COLLISION_FIG5C) return 0;
    return &COOK_FIGURE_5_ROWS[(int)which];
}

int cook_figure_5_normalize(int value) {
    int normalized = value % COOK_FIGURE_5_MODULUS;

    return normalized < 0 ? normalized + COOK_FIGURE_5_MODULUS : normalized;
}

int cook_figure_5_accepts_spacing(CollisionIdentity which, int spacing) {
    const CollisionIdentityRow *row = cook_figure_5(which);

    if (row == 0 || row->input_offset < 0) return 0;
    return cook_figure_5_normalize(spacing) ==
        cook_figure_5_normalize(row->input_offset);
}

int cook_figure_5_output_offset(CollisionIdentity which, int *offset_out) {
    const CollisionIdentityRow *row = cook_figure_5(which);

    if (row == 0 || offset_out == 0) return 0;
    *offset_out = cook_figure_5_normalize(row->output_offset);
    return 1;
}

const CookFigure10PassThrough *cook_figure_10_pass_through(
    CookFigure10Case which) {
    if (which < COOK_FIGURE10_FIRST_MOVING_AFTER_INVISIBLE ||
        which > COOK_FIGURE10_MOVING_AFTER_MOVING) {
        return 0;
    }
    return &COOK_FIGURE_10_ROWS[(int)which];
}

int cook_figure_10_accepts_c2_spacing(CookFigure10Case which, int spacing) {
    const CookFigure10PassThrough *row = cook_figure_10_pass_through(which);

    if (row == 0 || row->c2_spacing < 0) return 0;
    if (!cook_figure_5_accepts_spacing(COLLISION_FIG5C, row->c2_spacing)) {
        return 0;
    }
    return cook_figure_5_normalize(spacing) ==
        cook_figure_5_normalize(row->c2_spacing);
}

int cook_figure_10_accepts_ebar_spacing(CookFigure10Case which, int spacing) {
    const CookFigure10PassThrough *row = cook_figure_10_pass_through(which);

    if (row == 0 || row->ebar_spacing < 0) return 0;
    if (!cook_figure_5_accepts_spacing(COLLISION_FIG5B,
                                       row->ebar_spacing)) {
        return 0;
    }
    return cook_figure_5_normalize(spacing) ==
        cook_figure_5_normalize(row->ebar_spacing);
}

int cook_figure_10_regenerated_c2_offset(CookFigure10Case which,
                                         int *offset_out) {
    const CookFigure10PassThrough *row = cook_figure_10_pass_through(which);
    int figure5_offset = 0;

    if (row == 0 || offset_out == 0) return 0;
    if (!cook_figure_5_output_offset(COLLISION_FIG5A, &figure5_offset)) {
        return 0;
    }
    if (cook_figure_5_normalize(row->regenerated_c2_from_ebar) !=
        figure5_offset) {
        return 0;
    }
    *offset_out = figure5_offset;
    return 1;
}
