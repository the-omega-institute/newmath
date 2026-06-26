# G2N Matrix Completion

- status: `ok`
- E_rank allocation verdict: **negative**
- seeds/hyperparameters follow `_g2n_native_ledger.py`: np/torch 20260611, split 1701, bootstrap 500/314159, epochs 30, batch 256, lr 1e-3, lambda_budget 0.5.

## B_posthoc_horizon

| h | AUROC | UER | eval rows |
|---:|---:|---:|---:|
| 1 | 0.737486 [0.698811, 0.774685] | 0.170960 [0.148084, 0.194094] | 854 |
| 3 | 0.682477 [0.635003, 0.733482] | 0.220430 [0.183210, 0.259339] | 744 |
| 5 | 0.710364 [0.666395, 0.750271] | 0.198738 [0.162930, 0.236948] | 634 |
| 10 | 0.715188 [0.621742, 0.796608] | 0.126027 [0.078202, 0.175555] | 365 |

## E_rank

- pure E h=1 anchor: `0.738515205859875`
- E_rank delta ledger-uniform: `0.007466770`; 95% CI `[-0.002686442, 0.020330173]`; verdict **negative**
- H_rank permutation-control delta: `0.030546490`; 95% CI `[0.018277371, 0.045512244]`
- oracle ceiling oracle-uniform: `-0.015867561`

| arm | h=1 AUROC | h=5 AUROC |
|---|---:|---:|
| `pure_E` | 0.738515 [0.696238, 0.781118] | 0.710160 [0.657333, 0.760760] |
| `E_rank` | 0.706635 [0.666082, 0.746668] | 0.733177 [0.689686, 0.780273] |
| `H_rank` | 0.460512 [0.411233, 0.508418] | 0.541616 [0.473961, 0.610323] |

## G_oodh

- perturbed train label h=1 max |delta| vs `mse_train_*`: `6.78115612e-07`
- clean h=1 retention verdict: **retained**

| h | clean AUROC | clean UER |
|---:|---:|---:|
| 1 | 0.720317 [0.680839, 0.756774] | 0.071429 [0.054668, 0.088558] |
| 3 | 0.693392 [0.641508, 0.742727] | 0.110215 [0.081836, 0.140576] |
| 5 | 0.691268 [0.642629, 0.740754] | 0.111987 [0.079764, 0.150708] |
| 10 | 0.682383 [0.591868, 0.769363] | 0.126027 [0.076853, 0.183572] |

## Corrected OOD Representative Slices

| slice | h | E corrected AUROC | G_oodh corrected AUROC |
|---|---:|---:|---:|
| `background_tint_0p15` | 1 | 0.667612 [0.619115, 0.717583] | 0.751584 [0.718548, 0.785071] |
| `background_tint_0p15` | 3 | 0.646205 [0.602960, 0.689836] | 0.697711 [0.650332, 0.743807] |
| `background_tint_0p15` | 5 | 0.644756 [0.596314, 0.693120] | 0.680682 [0.636619, 0.722060] |
| `brightness_0p2` | 1 | 0.068662 [0.024321, 0.120899] | 0.990610 [0.981855, 0.997738] |
| `brightness_0p2` | 3 | 0.461707 [0.379929, 0.553856] | 0.644572 [0.565520, 0.723434] |
| `brightness_0p2` | 5 | 0.549861 [0.468641, 0.629711] | 0.693008 [0.620400, 0.758717] |
| `color_shift_0p2` | 1 | fail-closed | fail-closed |
| `color_shift_0p2` | 3 | fail-closed | fail-closed |
| `color_shift_0p2` | 5 | fail-closed | fail-closed |
| `gaussian_noise_10` | 1 | 0.551896 [0.383084, 0.697323] | 0.744787 [0.581282, 0.882459] |
| `gaussian_noise_10` | 3 | 0.516404 [0.450338, 0.580078] | 0.691849 [0.627248, 0.750268] |
| `gaussian_noise_10` | 5 | 0.564633 [0.497710, 0.637452] | 0.642826 [0.599579, 0.684557] |
| `occlusion_0p2` | 1 | 0.606666 [0.532695, 0.690429] | 0.770694 [0.707722, 0.828141] |
| `occlusion_0p2` | 3 | 0.588016 [0.539910, 0.638876] | 0.648986 [0.590678, 0.705618] |
| `occlusion_0p2` | 5 | 0.568251 [0.514792, 0.621137] | 0.650887 [0.600119, 0.700980] |

## Not Claimed

- No planning or control benefit is claimed.
- All allocation results are prediction-budget allocation only.
- No lambda or hyperparameter scan was performed.
- Single checkpoint/single latent export; episode bootstrap does not replace independent world seeds.
- B_posthoc_horizon is information-only.
