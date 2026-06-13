# OOD-aware training for the LAT port (phase2c protocol at the LAT level)

- clean anchor reproduces committed port AUROC 0.674576
- ood_aware training rows: 63945 (failure rate 0.793)
- strict final-strength positive families: ['background_tint']
- leave-one-out positive families (nonzero pooled): ['occlusion', 'brightness', 'background_tint', 'gaussian_noise']

## lat_ood_aware per-slice (eval)

| family | strength | vanilla UER | AUROC | UER | declared | claim |
| --- | --- | --- | --- | --- | --- | --- |
| `color_shift` | 0.1 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.002 [0.000, 0.005] | 0.998 [0.995, 1.000] | negative_or_inconclusive |
| `color_shift` | 0.2 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.000 [0.000, 0.000] | 1.000 [1.000, 1.000] | negative_or_inconclusive |
| `color_shift` | 0.3 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.000 [0.000, 0.000] | 1.000 [1.000, 1.000] | negative_or_inconclusive |
| `color_shift` | 0.4 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.000 [0.000, 0.000] | 1.000 [1.000, 1.000] | negative_or_inconclusive |
| `occlusion` | 0.12 | 0.500 | 0.708 [0.668, 0.746] | 0.118 [0.094, 0.141] | 0.615 [0.568, 0.658] | positive |
| `occlusion` | 0.2 | 0.934 | 0.707 [0.634, 0.769] | 0.028 [0.014, 0.042] | 0.965 [0.948, 0.980] | positive |
| `occlusion` | 0.28 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.000 [0.000, 0.000] | 1.000 [1.000, 1.000] | negative_or_inconclusive |
| `occlusion` | 0.36 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.000 [0.000, 0.000] | 1.000 [1.000, 1.000] | negative_or_inconclusive |
| `brightness` | 0.1 | 0.930 | 0.607 [0.503, 0.685] | 0.073 [0.047, 0.100] | 0.915 [0.884, 0.944] | positive |
| `brightness` | 0.2 | 0.998 | 0.606 [0.457, 0.765] | 0.015 [0.005, 0.026] | 0.985 [0.974, 0.995] | negative_or_inconclusive |
| `brightness` | 0.3 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.002 [0.000, 0.007] | 0.998 [0.993, 1.000] | negative_or_inconclusive |
| `brightness` | 0.4 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.001 [0.000, 0.004] | 0.999 [0.996, 1.000] | negative_or_inconclusive |
| `background_tint` | 0.15 | 0.314 | 0.735 [0.702, 0.770] | 0.120 [0.099, 0.146] | 0.370 [0.328, 0.415] | positive |
| `background_tint` | 0.3 | 0.323 | 0.761 [0.723, 0.792] | 0.113 [0.093, 0.133] | 0.380 [0.333, 0.419] | positive |
| `background_tint` | 0.45 | 0.324 | 0.770 [0.738, 0.802] | 0.109 [0.090, 0.128] | 0.380 [0.336, 0.419] | positive |
| `background_tint` | 0.6 | 0.324 | 0.769 [0.730, 0.801] | 0.112 [0.093, 0.135] | 0.378 [0.337, 0.422] | positive |
| `gaussian_noise` | 5 | 0.691 | 0.638 [0.601, 0.668] | 0.151 [0.118, 0.182] | 0.728 [0.684, 0.777] | positive |
| `gaussian_noise` | 10 | 0.990 | 0.843 [0.671, 0.956] | 0.019 [0.010, 0.028] | 0.980 [0.969, 0.990] | positive |
| `gaussian_noise` | 15 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.000 [0.000, 0.000] | 1.000 [1.000, 1.000] | negative_or_inconclusive |
| `gaussian_noise` | 25 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.000 [0.000, 0.000] | 1.000 [1.000, 1.000] | negative_or_inconclusive |

## leave-one-out (held-out family, nonzero pooled)

| held-out | AUROC | UER | vanilla UER | declared | claim |
| --- | --- | --- | --- | --- | --- |
| `color_shift` | 0.500 [0.500, 0.500] | 0.030 [0.018, 0.041] | 1.000 [1.000, 1.000] | 0.970 [0.959, 0.982] | negative_or_inconclusive |
| `occlusion` | 0.751 [0.719, 0.777] | 0.346 [0.304, 0.390] | 0.858 [0.847, 0.870] | 0.544 [0.498, 0.593] | positive |
| `brightness` | 0.664 [0.605, 0.724] | 0.601 [0.564, 0.638] | 0.982 [0.977, 0.986] | 0.384 [0.347, 0.421] | positive |
| `background_tint` | 0.699 [0.672, 0.731] | 0.156 [0.131, 0.181] | 0.321 [0.291, 0.352] | 0.319 [0.281, 0.363] | positive |
| `gaussian_noise` | 0.592 [0.557, 0.624] | 0.728 [0.705, 0.751] | 0.920 [0.913, 0.928] | 0.205 [0.181, 0.228] | positive |

## clean eval per arm (does OOD-aware training cost clean performance?)

- `lat_clean_only`: AUROC 0.675 [0.638, 0.712], UER 0.132 [0.108, 0.156], declared 0.243 [0.217, 0.272]
- `lat_ood_aware`: AUROC 0.721 [0.678, 0.759], UER 0.091 [0.076, 0.109], declared 0.348 [0.299, 0.394]
