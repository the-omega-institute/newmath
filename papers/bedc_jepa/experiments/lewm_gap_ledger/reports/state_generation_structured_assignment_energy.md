# State-Generation Structured Assignment Energy

- selected lambda: `10000.0`
- assignment rows: `1200`

| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |
|---|---:|---:|---:|---:|---:|
| `structured_assignment_energy` | -0.245845 | -0.571677 | -0.304134 | 0.138275 | -0.119654 |
| `anchor_depth_compatibility` | -0.22879 | -0.58407 | 0.0332661 | -0.135565 | 0.14269 |
| `scalar_mechanism` | -0.00499724 | -0.10215 | 0.108055 | -0.0208971 | 0.192193 |
| `set_context_mechanism` | -0.0324926 | 0 | -0.0551844 | -0.0422935 | 0.2526 |
| `base_perturbation_value` | -0.0681208 | -0.155576 | 0.0787014 | -0.127488 | 0.26347 |
| `mechanism_target_ceiling` | 1 | 1 | 1 | 1 | 0.999999 |

## Verdict

Structured assignment-energy learning does not improve held-out hard exact-budget capture over the scalar mechanism learner.
