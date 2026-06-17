# State-Generation Mechanism Target Learner

- device: `cuda`
- selected tail weight: `0.0`
- hard mean capture: `-0.00499724`
- base hard mean capture: `-0.0681208`
- target hard mean capture: `1`

| row | mean capture | budget-2 | budget-3 | budget-4 | label rho |
|---|---:|---:|---:|---:|---:|
| `mechanism_target_learner` | -0.00499724 | -0.10215 | 0.108055 | -0.0208971 | 0.192193 |
| `base_perturbation_value_learner` | -0.0681208 | -0.155576 | 0.0787014 | -0.127488 | 0.26347 |
| `mechanism_target_ceiling` | 1 | 1 | 1 | 1 | 0.999999 |

## Verdict

The non-leaky mechanism-target learner improves the mechanism route but does not close the held-out hard exact-budget gate.
