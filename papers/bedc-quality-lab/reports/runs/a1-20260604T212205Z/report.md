# Gap-Head Attribution Capsule

- Generated at: `2026-06-04T21:22:05.328899+00:00`
- Run id: `a1-20260604T212205Z`
- Artifact id: `gap_head_attribution_capsule`
- D5-O: `ready`
- D5-M: `blocked`
- Mechanism case: `Case C`
- Failed gate: `A1-HG3`

## Arms

| arm | AUROC | UER reduction | family | gate role |
| --- | ---: | ---: | --- | --- |
| `full` | 0.815589 +/- 0.044417 (95% CI +/- 0.015894) | 0.380870 +/- 0.085639 (95% CI +/- 0.030646) | `full` | `primary` |
| `h_only` | 0.646832 +/- 0.050907 (95% CI +/- 0.018217) | 0.283188 +/- 0.076242 (95% CI +/- 0.027283) | `h` | `diagnostic` |
| `h_centered_only` | 0.646832 +/- 0.050907 (95% CI +/- 0.018217) | 0.283188 +/- 0.076242 (95% CI +/- 0.027283) | `h` | `diagnostic` |
| `h_normalized_no_scale` | 0.557282 +/- 0.055716 (95% CI +/- 0.019938) | 0.272174 +/- 0.116958 (95% CI +/- 0.041853) | `h` | `diagnostic` |
| `h_direction_only` | 0.556672 +/- 0.055516 (95% CI +/- 0.019866) | 0.273333 +/- 0.120224 (95% CI +/- 0.043021) | `h` | `diagnostic` |
| `h_norm_only` | 0.597621 +/- 0.051906 (95% CI +/- 0.018574) | 0.285507 +/- 0.163146 (95% CI +/- 0.058381) | `h_control` | `A1-HG4-control` |
| `h_random_rotation` | 0.646842 +/- 0.050900 (95% CI +/- 0.018214) | 0.283188 +/- 0.076242 (95% CI +/- 0.027283) | `h_control` | `diagnostic` |
| `h_random_projection_lowdim` | 0.602693 +/- 0.064360 (95% CI +/- 0.023031) | 0.279130 +/- 0.119695 (95% CI +/- 0.042832) | `h_control` | `diagnostic` |
| `score_only` | 0.796595 +/- 0.051474 (95% CI +/- 0.018420) | 0.368116 +/- 0.086304 (95% CI +/- 0.030884) | `score` | `diagnostic` |
| `margin_only` | 0.568055 +/- 0.058254 (95% CI +/- 0.020846) | 0.266087 +/- 0.138560 (95% CI +/- 0.049583) | `margin` | `diagnostic` |
| `score_plus_margin` | 0.830649 +/- 0.041452 (95% CI +/- 0.014833) | 0.366667 +/- 0.063247 (95% CI +/- 0.022633) | `score_margin` | `A1-HG3-control` |
| `transition_delta_only` | 0.536348 +/- 0.066504 (95% CI +/- 0.023798) | 0.246957 +/- 0.142822 (95% CI +/- 0.051108) | `transition` | `diagnostic` |
| `quality_scalars_only` | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) | 0.258841 +/- 0.264529 (95% CI +/- 0.094660) | `quality` | `diagnostic` |
| `h_plus_margin` | 0.665109 +/- 0.052792 (95% CI +/- 0.018891) | 0.336812 +/- 0.100190 (95% CI +/- 0.035853) | `combined` | `diagnostic` |
| `h_plus_transition` | 0.649792 +/- 0.057584 (95% CI +/- 0.020606) | 0.306667 +/- 0.086684 (95% CI +/- 0.031020) | `combined` | `diagnostic` |
| `h_plus_quality` | 0.646832 +/- 0.050907 (95% CI +/- 0.018217) | 0.283188 +/- 0.076242 (95% CI +/- 0.027283) | `combined` | `diagnostic` |
| `full_without_h` | 0.801250 +/- 0.044209 (95% CI +/- 0.015820) | 0.376232 +/- 0.088735 (95% CI +/- 0.031754) | `ablation` | `diagnostic` |
| `full_without_score` | 0.664244 +/- 0.051333 (95% CI +/- 0.018369) | 0.331884 +/- 0.092706 (95% CI +/- 0.033174) | `ablation` | `diagnostic` |
| `full_without_margin` | 0.805031 +/- 0.046021 (95% CI +/- 0.016469) | 0.368116 +/- 0.083572 (95% CI +/- 0.029906) | `ablation` | `diagnostic` |
| `full_without_transition` | 0.826162 +/- 0.049520 (95% CI +/- 0.017720) | 0.388406 +/- 0.087056 (95% CI +/- 0.031153) | `ablation` | `A1-HG5-ablation` |
| `full_without_quality_scalars` | 0.815589 +/- 0.044417 (95% CI +/- 0.015894) | 0.380870 +/- 0.085639 (95% CI +/- 0.030646) | `ablation` | `diagnostic` |
| `full_residualized_against_score_margin` | 0.800806 +/- 0.051129 (95% CI +/- 0.018296) | 0.366667 +/- 0.087288 (95% CI +/- 0.031236) | `residualized_attribution` | `A4-HG2-primary` |
| `full_without_score_and_margin` | 0.649792 +/- 0.057584 (95% CI +/- 0.020606) | 0.306667 +/- 0.086684 (95% CI +/- 0.031020) | `residualized_attribution` | `A4-HG3-primary` |
| `matched_random` | 0.493183 +/- 0.096779 (95% CI +/- 0.034632) | 0.242899 +/- 0.099825 (95% CI +/- 0.035722) | `negative_control` | `A1-HG1-control` |

## A1 Hardgates

| gate | status |
| --- | --- |
| `A1-HG1` | `pass` |
| `A1-HG2` | `pass` |
| `A1-HG3` | `fail` |
| `A1-HG4` | `pass` |
| `A1-HG5` | `pass` |
| `A1-HG6` | `fail` |

## A4 Hardgates

| gate | status |
| --- | --- |
| `A4-HG1` | `pass` |
| `A4-HG2` | `pass` |
| `A4-HG3` | `pass` |
| `A4-HG4` | `pass` |
| `A4-HG5` | `fail` |

## Claim Capsule Hardgates

| gate | status |
| --- | --- |
| `CC-HG1` | `pass` |
| `CC-HG2` | `pass` |
| `CC-HG3` | `pass` |
| `CC-HG4` | `pass` |
| `CC-HG5` | `pass` |
| `CC-HG6` | `pass` |
| `CC-HG7` | `pass` |

## Scope

- global model quality
- full LeJEPA reproduction
- full TensorNameCert
- LLM behavior quality
- mechanism closure unless D5-M
