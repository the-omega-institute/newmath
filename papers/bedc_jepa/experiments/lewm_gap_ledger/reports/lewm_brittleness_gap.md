# Phase 2a: brittleness gap ledger

- latent: `tworooms_latent_large.npz`; H5: `_tworoom_prefix_large.h5`
- protocol: clean train split fits probe + `B_denoised_agent_room_only` prediction_error gap head; perturbed eval is OOD only
- failure truth: `prediction_mse > 0.076702` (clean train p75)
- bootstrap: 300 resamples, eval episodes as unit
- conclusion: **mixed** - positive on ['background_tint']; fail-closed negative_or_inconclusive on ['color_shift', 'occlusion', 'brightness', 'gaussian_noise']

## Curves

### color_shift

- claim: **negative_or_inconclusive**; final mse-clean delta=3.323858; final vanilla UER-clean delta=0.7687; final BEDC-vs-vanilla UER delta=0.0000; min nonzero AUROC=0.5000

| strength | mean MSE | vanilla UER | BEDC UER | AUROC | mean gap |
|---:|---:|---:|---:|---:|---:|
| 0 | 0.066618 | 0.2313 | 0.1680 | 0.7314 | 0.2476 |
| 0.1 | 0.412297 | 1.0000 | 0.8734 | 0.5000 | 0.2737 |
| 0.2 | 1.387583 | 1.0000 | 0.9170 | 0.5000 | 0.2367 |
| 0.3 | 2.479319 | 1.0000 | 1.0000 | 0.5000 | 0.0895 |
| 0.4 | 3.390476 | 1.0000 | 1.0000 | 0.5000 | 0.0783 |

### occlusion

- claim: **negative_or_inconclusive**; final mse-clean delta=0.589671; final vanilla UER-clean delta=0.7687; final BEDC-vs-vanilla UER delta=-0.1100; min nonzero AUROC=0.5000

| strength | mean MSE | vanilla UER | BEDC UER | AUROC | mean gap |
|---:|---:|---:|---:|---:|---:|
| 0 | 0.066618 | 0.2313 | 0.1680 | 0.7314 | 0.2476 |
| 0.12 | 0.094631 | 0.5052 | 0.4253 | 0.6776 | 0.2396 |
| 0.2 | 0.283649 | 0.9346 | 0.8537 | 0.6025 | 0.2346 |
| 0.28 | 0.690654 | 1.0000 | 0.8247 | 0.5000 | 0.3298 |
| 0.36 | 0.656288 | 1.0000 | 0.8900 | 0.5000 | 0.2861 |

### brightness

- claim: **negative_or_inconclusive**; final mse-clean delta=0.486017; final vanilla UER-clean delta=0.7687; final BEDC-vs-vanilla UER delta=-0.0602; min nonzero AUROC=0.4174

| strength | mean MSE | vanilla UER | BEDC UER | AUROC | mean gap |
|---:|---:|---:|---:|---:|---:|
| 0 | 0.066618 | 0.2313 | 0.1680 | 0.7314 | 0.2476 |
| 0.1 | 0.165079 | 0.9305 | 0.8786 | 0.5764 | 0.2221 |
| 0.2 | 0.298541 | 0.9979 | 0.9450 | 0.4174 | 0.2176 |
| 0.3 | 0.428685 | 0.9990 | 0.9388 | 0.4943 | 0.2170 |
| 0.4 | 0.552635 | 1.0000 | 0.9398 | 0.5000 | 0.2173 |

### background_tint

- claim: **positive**; final mse-clean delta=0.150089; final vanilla UER-clean delta=0.0954; final BEDC-vs-vanilla UER delta=-0.0716; min nonzero AUROC=0.6846

| strength | mean MSE | vanilla UER | BEDC UER | AUROC | mean gap |
|---:|---:|---:|---:|---:|---:|
| 0 | 0.066618 | 0.2313 | 0.1680 | 0.7314 | 0.2476 |
| 0.15 | 0.090848 | 0.3174 | 0.2459 | 0.6846 | 0.2493 |
| 0.3 | 0.133058 | 0.3237 | 0.2500 | 0.7003 | 0.2498 |
| 0.45 | 0.174912 | 0.3268 | 0.2531 | 0.7113 | 0.2503 |
| 0.6 | 0.216707 | 0.3268 | 0.2552 | 0.7187 | 0.2510 |

### gaussian_noise

- claim: **negative_or_inconclusive**; final mse-clean delta=0.840052; final vanilla UER-clean delta=0.7687; final BEDC-vs-vanilla UER delta=-0.1286; min nonzero AUROC=0.5000

| strength | mean MSE | vanilla UER | BEDC UER | AUROC | mean gap |
|---:|---:|---:|---:|---:|---:|
| 0 | 0.066618 | 0.2313 | 0.1680 | 0.7314 | 0.2476 |
| 5 | 0.103773 | 0.6909 | 0.5861 | 0.6318 | 0.2611 |
| 10 | 0.221438 | 0.9907 | 0.8662 | 0.6412 | 0.2777 |
| 15 | 0.467683 | 1.0000 | 0.8797 | 0.5000 | 0.2908 |
| 25 | 0.906670 | 1.0000 | 0.8714 | 0.5000 | 0.3150 |

## CI Detail

### color_shift

| strength | mean MSE CI | vanilla UER CI | BEDC UER CI | AUROC CI |
|---:|---:|---:|---:|---:|
| 0 | 0.0666 [0.0644, 0.0691] | 0.2313 [0.2044, 0.2593] | 0.1680 [0.1442, 0.1967] | 0.7314 [0.6842, 0.7674] |
| 0.1 | 0.4123 [0.4006, 0.4229] | 1.0000 [1.0000, 1.0000] | 0.8734 [0.8488, 0.8982] | 0.5000 [0.5000, 0.5000] |
| 0.2 | 1.3876 [1.3618, 1.4113] | 1.0000 [1.0000, 1.0000] | 0.9170 [0.8923, 0.9370] | 0.5000 [0.5000, 0.5000] |
| 0.3 | 2.4793 [2.4508, 2.5080] | 1.0000 [1.0000, 1.0000] | 1.0000 [1.0000, 1.0000] | 0.5000 [0.5000, 0.5000] |
| 0.4 | 3.3905 [3.3544, 3.4302] | 1.0000 [1.0000, 1.0000] | 1.0000 [1.0000, 1.0000] | 0.5000 [0.5000, 0.5000] |

### occlusion

| strength | mean MSE CI | vanilla UER CI | BEDC UER CI | AUROC CI |
|---:|---:|---:|---:|---:|
| 0 | 0.0666 [0.0643, 0.0696] | 0.2313 [0.2062, 0.2596] | 0.1680 [0.1452, 0.1947] | 0.7314 [0.6954, 0.7670] |
| 0.12 | 0.0946 [0.0887, 0.1009] | 0.5052 [0.4678, 0.5469] | 0.4253 [0.3916, 0.4614] | 0.6776 [0.6403, 0.7084] |
| 0.2 | 0.2836 [0.2453, 0.3220] | 0.9346 [0.9113, 0.9599] | 0.8537 [0.8250, 0.8840] | 0.6025 [0.5288, 0.6755] |
| 0.28 | 0.6907 [0.6258, 0.7436] | 1.0000 [1.0000, 1.0000] | 0.8247 [0.7938, 0.8559] | 0.5000 [0.5000, 0.5000] |
| 0.36 | 0.6563 [0.6042, 0.7103] | 1.0000 [1.0000, 1.0000] | 0.8900 [0.8697, 0.9102] | 0.5000 [0.5000, 0.5000] |

### brightness

| strength | mean MSE CI | vanilla UER CI | BEDC UER CI | AUROC CI |
|---:|---:|---:|---:|---:|
| 0 | 0.0666 [0.0644, 0.0693] | 0.2313 [0.2046, 0.2574] | 0.1680 [0.1451, 0.1889] | 0.7314 [0.6926, 0.7684] |
| 0.1 | 0.1651 [0.1592, 0.1710] | 0.9305 [0.9107, 0.9477] | 0.8786 [0.8522, 0.9027] | 0.5764 [0.5079, 0.6636] |
| 0.2 | 0.2985 [0.2860, 0.3102] | 0.9979 [0.9948, 1.0000] | 0.9450 [0.9285, 0.9599] | 0.4174 [0.2231, 0.6205] |
| 0.3 | 0.4287 [0.4098, 0.4469] | 0.9990 [0.9968, 1.0000] | 0.9388 [0.9223, 0.9532] | 0.4943 [0.4566, 0.5295] |
| 0.4 | 0.5526 [0.5310, 0.5729] | 1.0000 [1.0000, 1.0000] | 0.9398 [0.9212, 0.9569] | 0.5000 [0.5000, 0.5000] |

### background_tint

| strength | mean MSE CI | vanilla UER CI | BEDC UER CI | AUROC CI |
|---:|---:|---:|---:|---:|
| 0 | 0.0666 [0.0645, 0.0693] | 0.2313 [0.2077, 0.2614] | 0.1680 [0.1416, 0.1927] | 0.7314 [0.6899, 0.7712] |
| 0.15 | 0.0908 [0.0833, 0.0987] | 0.3174 [0.2867, 0.3510] | 0.2459 [0.2141, 0.2808] | 0.6846 [0.6527, 0.7188] |
| 0.3 | 0.1331 [0.1145, 0.1551] | 0.3237 [0.2869, 0.3576] | 0.2500 [0.2141, 0.2818] | 0.7003 [0.6669, 0.7359] |
| 0.45 | 0.1749 [0.1426, 0.2084] | 0.3268 [0.2975, 0.3609] | 0.2531 [0.2207, 0.2859] | 0.7113 [0.6717, 0.7394] |
| 0.6 | 0.2167 [0.1827, 0.2609] | 0.3268 [0.2928, 0.3555] | 0.2552 [0.2221, 0.2938] | 0.7187 [0.6852, 0.7539] |

### gaussian_noise

| strength | mean MSE CI | vanilla UER CI | BEDC UER CI | AUROC CI |
|---:|---:|---:|---:|---:|
| 0 | 0.0666 [0.0644, 0.0693] | 0.2313 [0.2047, 0.2613] | 0.1680 [0.1459, 0.1936] | 0.7314 [0.6878, 0.7706] |
| 5 | 0.1038 [0.1004, 0.1073] | 0.6909 [0.6649, 0.7217] | 0.5861 [0.5476, 0.6207] | 0.6318 [0.5928, 0.6704] |
| 10 | 0.2214 [0.2136, 0.2310] | 0.9907 [0.9838, 0.9959] | 0.8662 [0.8397, 0.8917] | 0.6412 [0.3850, 0.8567] |
| 15 | 0.4677 [0.4513, 0.4840] | 1.0000 [1.0000, 1.0000] | 0.8797 [0.8573, 0.8999] | 0.5000 [0.5000, 0.5000] |
| 25 | 0.9067 [0.8842, 0.9292] | 1.0000 [1.0000, 1.0000] | 0.8714 [0.8484, 0.8941] | 0.5000 [0.5000, 0.5000] |

## Debt

- coverage_debt / statistical_design: single LeWM tworooms latent export with 278 episodes/4991 transitions; episode bootstrap does not replace independent world seeds
- source_debt / distinction_probe:near_target: eval accuracy 0.5902 below 0.60 separability sanity threshold
- source_debt / background_tint_mask: background_tint uses RGB edge/color heuristic foreground mask, not simulator segmentation; failures are reported fail-closed

Demo samples: `reports/brittleness_demo_samples.npz`
