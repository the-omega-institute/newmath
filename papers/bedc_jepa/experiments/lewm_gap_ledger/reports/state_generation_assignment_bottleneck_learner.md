# State-Generation Assignment Bottleneck Learner

- bottleneck selected lambda: `1.0`
- control selected lambda: `1.0`

| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |
|---|---:|---:|---:|---:|---:|
| `assignment_bottleneck` | -0.444673 | -0.394223 | -0.802745 | -0.137052 | 0.218586 |
| `matched_nonmechanism_control` | -1.11017 | -1.63746 | -1.41618 | -0.276867 | 0.0526315 |
| `mechanism_target_ceiling` | 1 | 1 | 1 | 1 | 1 |

## Verdict

The assignment-bearing bottleneck learner beats the matched non-mechanism control but does not close all hard exact-budget budgets.
