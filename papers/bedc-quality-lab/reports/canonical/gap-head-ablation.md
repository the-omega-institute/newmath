# Gap-Head Ablation

- Generated at: `2026-06-13T08:50:00.802938+00:00`
- Hardgate status: `fail`
- Sample count: `384`
- Low sample count: `96`
- Seed count: `30`
- Delta threshold: `0.02`

## Arms

| arm | failure-detection AUROC | ECE | UnloggedErrorRate | critical unlogged error rate |
| --- | ---: | ---: | ---: | ---: |
| `vanilla` | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) | 0.505797 +/- 0.054620 (95% CI +/- 0.019545) | 0.505797 +/- 0.054620 (95% CI +/- 0.019545) | 0.505797 +/- 0.054620 (95% CI +/- 0.019545) |
| `learned_gap_head_on_h` | 0.815589 +/- 0.044417 (95% CI +/- 0.015894) | 0.115027 +/- 0.029219 (95% CI +/- 0.010456) | 0.124928 +/- 0.063140 (95% CI +/- 0.022594) | 0.000580 +/- 0.002206 (95% CI +/- 0.000789) |
| `matched_random_gap_head` | 0.493183 +/- 0.096779 (95% CI +/- 0.034632) | 0.122031 +/- 0.048069 (95% CI +/- 0.017201) | 0.262899 +/- 0.086164 (95% CI +/- 0.030833) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) |
| `drop_prediction_error_channel` | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) | 0.505797 +/- 0.054620 (95% CI +/- 0.019545) | 0.505797 +/- 0.054620 (95% CI +/- 0.019545) | 0.001159 +/- 0.003775 (95% CI +/- 0.001351) |
| `drop_low_margin_channel` | 0.815589 +/- 0.044417 (95% CI +/- 0.015894) | 0.115027 +/- 0.029219 (95% CI +/- 0.010456) | 0.124928 +/- 0.063140 (95% CI +/- 0.022594) | 0.000870 +/- 0.002653 (95% CI +/- 0.000949) |
| `drop_transition_unstable_channel` | 0.815589 +/- 0.044417 (95% CI +/- 0.015894) | 0.115027 +/- 0.029219 (95% CI +/- 0.010456) | 0.124928 +/- 0.063140 (95% CI +/- 0.022594) | 0.000870 +/- 0.003501 (95% CI +/- 0.001253) |
| `drop_off_target_intervention_channel` | 0.815589 +/- 0.044417 (95% CI +/- 0.015894) | 0.115027 +/- 0.029219 (95% CI +/- 0.010456) | 0.124928 +/- 0.063140 (95% CI +/- 0.022594) | 0.032174 +/- 0.023858 (95% CI +/- 0.008537) |
| `pooled_any_gap_head_on_h` | 0.590058 +/- 0.060939 (95% CI +/- 0.021807) | 0.455628 +/- 0.052033 (95% CI +/- 0.018620) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) |
| `no_h_conditioning_gap_head` | 0.642169 +/- 0.046293 (95% CI +/- 0.016566) | 0.162039 +/- 0.047978 (95% CI +/- 0.017169) | 0.221159 +/- 0.057485 (95% CI +/- 0.020571) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) |
| `low_sample_full_gap_head_on_h` | 0.746431 +/- 0.090805 (95% CI +/- 0.032494) | 0.202051 +/- 0.048304 (95% CI +/- 0.017285) | 0.183908 +/- 0.080658 (95% CI +/- 0.028863) | 0.006897 +/- 0.014029 (95% CI +/- 0.005020) |

## Factor Attribution

| factor | ablated arm | AUROC delta | AUROC drop CI low | status |
| --- | --- | ---: | ---: | --- |
| `learned_head_conditioning` | `no_h_conditioning_gap_head` | -0.173420 | 0.155505 | `pass` |
| `prediction_error_channel` | `drop_prediction_error_channel` | -0.315589 | 0.299695 | `pass` |
| `low_margin_channel` | `drop_low_margin_channel` | 0.000000 | 0.000000 | `fail` |
| `transition_unstable_channel` | `drop_transition_unstable_channel` | 0.000000 | 0.000000 | `fail` |
| `off_target_intervention_channel` | `drop_off_target_intervention_channel` | 0.000000 | 0.000000 | `fail` |
| `per_channel_head_capacity` | `pooled_any_gap_head_on_h` | -0.225531 | 0.194784 | `pass` |
| `sample_count` | `low_sample_full_gap_head_on_h` | -0.069158 | 0.037347 | `pass` |

## Hardgate

- `$.hardgate.status`: `fail`
- Positive-discovery pointer: `$.factor_attribution.learned_head.auroc_delta`
- Control pointer: `$.control_protocol`

## Boundary

- No global quality claim.
- No transfer-surface claim.
- No large-model extrapolation.
- No inference-time use of z, z_pair, gap_label, prediction_error, or eval_gap_labels.
