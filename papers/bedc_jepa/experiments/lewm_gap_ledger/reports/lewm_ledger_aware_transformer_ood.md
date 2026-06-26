# LAT port OOD arm: clean-trained ledger head under perturbation

- clean anchor: eval AUROC 0.675 (reproduces the committed port report)
- failure truth: perturbed prediction_mse > 0.076702 (clean train p75)
- fail-closed single-class slices: color_shift@0.1, color_shift@0.2, color_shift@0.3, color_shift@0.4, occlusion@0.28, occlusion@0.36, brightness@0.3, brightness@0.4, gaussian_noise@15, gaussian_noise@25

| family | strength | vanilla UER (=failure rate) | LAT AUROC | LAT UER | declared gap rate | phase2a logistic AUROC |
| --- | --- | --- | --- | --- | --- | --- |
| `color_shift` | 0.1 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.763 [0.732, 0.791] | 0.237 [0.209, 0.268] | 0.500 |
| `color_shift` | 0.2 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.893 [0.870, 0.914] | 0.107 [0.086, 0.130] | 0.500 |
| `color_shift` | 0.3 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.988 [0.981, 0.994] | 0.012 [0.006, 0.019] | 0.500 |
| `color_shift` | 0.4 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 1.000 [1.000, 1.000] | 0.000 [0.000, 0.000] | 0.500 |
| `occlusion` | 0.12 | 0.500 | 0.624 [0.589, 0.657] | 0.337 [0.306, 0.368] | 0.239 [0.212, 0.269] | 0.678 |
| `occlusion` | 0.2 | 0.934 | 0.617 [0.543, 0.699] | 0.698 [0.660, 0.732] | 0.242 [0.214, 0.268] | 0.602 |
| `occlusion` | 0.28 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.822 [0.794, 0.847] | 0.178 [0.153, 0.206] | 0.500 |
| `occlusion` | 0.36 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.842 [0.810, 0.868] | 0.158 [0.132, 0.190] | 0.500 |
| `brightness` | 0.1 | 0.930 | 0.642 [0.567, 0.719] | 0.714 [0.683, 0.743] | 0.225 [0.202, 0.249] | 0.576 |
| `brightness` | 0.2 | 0.998 | 0.511 [0.404, 0.627] | 0.781 [0.752, 0.807] | 0.217 [0.191, 0.246] | 0.417 |
| `brightness` | 0.3 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.778 [0.750, 0.807] | 0.222 [0.193, 0.250] | 0.494 |
| `brightness` | 0.4 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.779 [0.753, 0.807] | 0.221 [0.193, 0.247] | 0.500 |
| `background_tint` | 0.15 | 0.314 | 0.650 [0.619, 0.682] | 0.193 [0.166, 0.221] | 0.245 [0.222, 0.273] | 0.685 |
| `background_tint` | 0.3 | 0.323 | 0.641 [0.613, 0.672] | 0.200 [0.174, 0.228] | 0.245 [0.219, 0.273] | 0.700 |
| `background_tint` | 0.45 | 0.324 | 0.624 [0.594, 0.659] | 0.210 [0.184, 0.238] | 0.241 [0.216, 0.268] | 0.711 |
| `background_tint` | 0.6 | 0.324 | 0.623 [0.593, 0.655] | 0.212 [0.185, 0.242] | 0.240 [0.215, 0.267] | 0.719 |
| `gaussian_noise` | 5 | 0.691 | 0.627 [0.594, 0.658] | 0.482 [0.447, 0.515] | 0.267 [0.242, 0.296] | 0.632 |
| `gaussian_noise` | 10 | 0.990 | 0.706 [0.532, 0.845] | 0.710 [0.675, 0.738] | 0.281 [0.256, 0.314] | 0.641 |
| `gaussian_noise` | 15 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.685 [0.656, 0.714] | 0.315 [0.286, 0.344] | 0.500 |
| `gaussian_noise` | 25 | 1.000 | 0.500 [0.500, 0.500] (single-class) | 0.555 [0.522, 0.587] | 0.445 [0.413, 0.478] | 0.500 |

Summary per family (strengths with AUROC ci95_low > 0.5 / single-class fail-closed):

- `color_shift`: detectable at none; single-class at [0.1, 0.2, 0.3, 0.4]
- `occlusion`: detectable at [0.12, 0.2]; single-class at [0.28, 0.36]
- `brightness`: detectable at [0.1]; single-class at [0.3, 0.4]
- `background_tint`: detectable at [0.15, 0.3, 0.45, 0.6]; single-class at none
- `gaussian_noise`: detectable at [5.0, 10.0]; single-class at [15.0, 25.0]
