# State-Generation Budget-Conditioned Assignment Bottleneck

| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |
|---|---:|---:|---:|---:|---:|
| `budget_conditioned_assignment_bottleneck` | -0.834385 | -1.67109 | -0.611341 | -0.220728 | 0.227293 |
| `budget_conditioned_nonmechanism_control` | -0.307198 | 0.238 | -0.738813 | -0.420781 | 0.304827 |
| `mechanism_target_ceiling` | 1 | 1 | 1 | 1 | 1 |

## Gates

- exact-budget cardinality: `True`
- forced-delta label prediction parity checked: `True`
- bottleneck/control mean MSE ratio: `1.03579`
- material prediction advantage: `False`

## Verdict

Budget-specific assignment-bottleneck training fails closed against the matched budget-conditioned non-mechanism control.
