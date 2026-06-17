# State-Generation Set-Context Mechanism Learner

- selected lambda: `10000.0`
- selected tail weight: `0.0`

| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |
|---|---:|---:|---:|---:|---:|
| `set_context_mechanism` | -0.0324926 | 0 | -0.0551844 | -0.0422935 | 0.2526 |
| `mechanism_scalar_learner` | -0.00499724 | -0.10215 | 0.108055 | -0.0208971 | 0.192193 |
| `base_perturbation_value` | -0.0681208 | -0.155576 | 0.0787014 | -0.127488 | 0.26347 |
| `mechanism_target_ceiling` | 1 | 1 | 1 | 1 | 0.999999 |

## Verdict

Set-context mechanism learning improves the hard mechanism route but does not close all hard exact-budget budgets.
