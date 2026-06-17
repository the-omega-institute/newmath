# State-Generation Hard-Regime Descriptors

- hard episodes: `[81, 115, 145, 193, 201, 213, 277]`
- strongest descriptor: `best_seed_score_entropy_mean`
- strongest p: `0.256549`

| descriptor | direction | hard mean | non-hard mean | gap | p |
|---|---|---:|---:|---:|---:|
| `best_seed_score_margin_mean` | lower | 1.27382 | 1.253 | 0.0208157 | 0.579484 |
| `best_seed_score_entropy_mean` | higher | 1.0572 | 1.02525 | 0.0319468 | 0.256549 |
| `best_seed_score_spread_mean` | higher | 1.21807 | 1.31153 | -0.0934571 | 0.929014 |
| `row_argmin_pair_disagreement_mean` | higher | 0.311734 | 0.310392 | 0.00134215 | 0.468306 |
| `row_argmin_majority_disagreement_mean` | higher | 0.197939 | 0.188091 | 0.00984734 | 0.354329 |
| `exact_budget_assignment_flip_mean` | higher | 0.213616 | 0.211503 | 0.0021132 | 0.487303 |
| `rollout_step_norm_mean` | higher | 16.6484 | 17.0805 | -0.432087 | 0.770446 |
| `rollout_step_norm_max` | higher | 20.723 | 21.171 | -0.447992 | 0.85103 |
| `rollout_curvature_mean` | higher | 28.468 | 29.0686 | -0.600588 | 0.69906 |
| `rollout_curvature_max` | higher | 34.227 | 34.9138 | -0.686715 | 0.753249 |
| `rollout_valid_fraction` | lower | 0.85603 | 0.848325 | 0.00770492 | 0.54769 |
| `best_seed_margin_p10` | lower | 0.39587 | 0.388512 | 0.00735753 | 0.563887 |
| `assignment_flip_p90` | higher | 0.433333 | 0.422569 | 0.0107639 | 0.441712 |

## Verdict

The tested fixed scorer and rollout descriptors do not strongly separate the recurring hard episodes; the next route needs richer causal perturbations or environment-state descriptors.
