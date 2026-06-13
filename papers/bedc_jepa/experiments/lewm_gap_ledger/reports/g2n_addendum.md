# G2N Addendum

- status: `ok`
- scope: exploratory addendum; no accepted report files were modified.
- corrected OOD fixes future-token availability for perturb eval and does not overturn the main report.

## Perturbed pred_z Cache

- output: `reports/g2n_labels_perturbed_predz.npz`
- h=1 max |delta| vs `g2n_labels_perturbed.npz` err_at_h: `1.66840058e-07`
- tolerance: `1e-06`

## Corrected OOD

- masked column is the accepted main report value with zero/masked future tokens.
- corrected column uses true perturbed rollout future tokens from this addendum.
- single-class truth is fail-closed for AUROC.

| arm | slice | h | masked AUROC | corrected AUROC |
|---|---|---:|---:|---:|
| `E` | `background_tint_0p15` | 1 | 0.548782 [0.506451, 0.595062] | 0.667612 [0.619115, 0.717583] |
| `E` | `background_tint_0p15` | 3 | 0.542817 [0.491492, 0.588599] | 0.646205 [0.602960, 0.689836] |
| `E` | `background_tint_0p15` | 5 | 0.609988 [0.548795, 0.673817] | 0.644756 [0.596314, 0.693120] |
| `E` | `brightness_0p2` | 1 | 0.389671 [0.128640, 0.654790] | 0.068662 [0.024321, 0.120899] |
| `E` | `brightness_0p2` | 3 | 0.504594 [0.404805, 0.606449] | 0.461707 [0.379929, 0.553856] |
| `E` | `brightness_0p2` | 5 | 0.510618 [0.425866, 0.597190] | 0.549861 [0.468641, 0.629711] |
| `E` | `color_shift_0p2` | 1 | 0.500000 [0.500000, 0.500000] | fail-closed |
| `E` | `color_shift_0p2` | 3 | 0.500000 [0.500000, 0.500000] | fail-closed |
| `E` | `color_shift_0p2` | 5 | 0.500000 [0.500000, 0.500000] | fail-closed |
| `E` | `gaussian_noise_10` | 1 | 0.484242 [0.326397, 0.662283] | 0.551896 [0.383084, 0.697323] |
| `E` | `gaussian_noise_10` | 3 | 0.555869 [0.496362, 0.617505] | 0.516404 [0.450338, 0.580078] |
| `E` | `gaussian_noise_10` | 5 | 0.553366 [0.506121, 0.608024] | 0.564633 [0.497710, 0.637452] |
| `E` | `occlusion_0p2` | 1 | 0.550920 [0.473279, 0.619338] | 0.606666 [0.532695, 0.690429] |
| `E` | `occlusion_0p2` | 3 | 0.544890 [0.482098, 0.613369] | 0.588016 [0.539910, 0.638876] |
| `E` | `occlusion_0p2` | 5 | 0.516723 [0.449799, 0.578622] | 0.568251 [0.514792, 0.621137] |
| `F` | `background_tint_0p15` | 1 | 0.666024 [0.622771, 0.710397] | 0.673123 [0.629935, 0.712355] |
| `F` | `background_tint_0p15` | 3 | 0.578132 [0.536236, 0.622183] | 0.629145 [0.575421, 0.676537] |
| `F` | `background_tint_0p15` | 5 | 0.543042 [0.495153, 0.595780] | 0.607398 [0.550087, 0.658568] |
| `F` | `brightness_0p2` | 1 | 0.758216 [0.500000, 0.856569] | 0.626761 [0.552410, 0.703224] |
| `F` | `brightness_0p2` | 3 | 0.589159 [0.503923, 0.665493] | 0.524622 [0.455220, 0.604492] |
| `F` | `brightness_0p2` | 5 | 0.480187 [0.406391, 0.557779] | 0.532564 [0.469086, 0.603567] |
| `F` | `color_shift_0p2` | 1 | 0.500000 [0.500000, 0.500000] | fail-closed |
| `F` | `color_shift_0p2` | 3 | 0.500000 [0.500000, 0.500000] | fail-closed |
| `F` | `color_shift_0p2` | 5 | 0.500000 [0.500000, 0.500000] | fail-closed |
| `F` | `gaussian_noise_10` | 1 | 0.590284 [0.388694, 0.784180] | 0.703199 [0.507723, 0.866546] |
| `F` | `gaussian_noise_10` | 3 | 0.603069 [0.542086, 0.666070] | 0.554726 [0.485983, 0.625632] |
| `F` | `gaussian_noise_10` | 5 | 0.496809 [0.441489, 0.550661] | 0.516756 [0.466136, 0.567879] |
| `F` | `occlusion_0p2` | 1 | 0.706359 [0.644782, 0.774497] | 0.629222 [0.557537, 0.699296] |
| `F` | `occlusion_0p2` | 3 | 0.571270 [0.509124, 0.632711] | 0.571261 [0.515047, 0.620232] |
| `F` | `occlusion_0p2` | 5 | 0.532742 [0.475059, 0.591972] | 0.548882 [0.494444, 0.600671] |

## Exploratory Allocation

- exploratory: true; outside predeclared Outcome 2 because E was not the predeclared main arm.
- delta E-uniform per emitted-step MSE: `0.007214424`
- 95% CI (500 episode bootstraps, seed 314159): `[-0.000619344, 0.017141858]`
- verdict: `negative_or_inconclusive`

## Anchors

- perturbed pred_z h=1 max |delta|: `1.66840058e-07`
- E clean h=1,q75 AUROC: `0.738515205859875`
- F clean h=1,q75 AUROC: `0.691660423902598`

## Not Claimed

- This is an exploratory addendum and a separate report.
- No existing accepted report or label file is modified.
- The exploratory allocation test is outside predeclared Outcome 2; arm E was not the predeclared primary arm.
- Corrected OOD repairs future-token availability for perturb eval and does not overturn the main report.
- Results are reported regardless of direction.
