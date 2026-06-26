# State-Generation Assignment-Contrastive Mechanism

- selected lambda: `1e-05`
- train pair rows: `1200`

| row | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard label rho |
|---|---:|---:|---:|---:|---:|
| `assignment_contrastive` | -1.08731 | -2.03264 | -0.79226 | -0.437028 | 0.0442852 |
| `scalar_mechanism` | -0.00499724 | -0.10215 | 0.108055 | -0.0208971 | 0.192193 |
| `set_context_mechanism` | -0.0324926 | 0 | -0.0551844 | -0.0422935 | 0.2526 |
| `base_perturbation_value` | -0.0681208 | -0.155576 | 0.0787014 | -0.127488 | 0.26347 |
| `mechanism_target_ceiling` | 1 | 1 | 1 | 1 | 0.999999 |

## Verdict

Assignment-contrastive mechanism learning does not improve held-out hard exact-budget capture over the scalar mechanism learner.
