# State-Generation Hard Perturbation Episode Transfer

- selected candidate: `mix_learner_fixed_0.50`
- candidate count: `34`

| slice | mean capture | budget-2 | budget-3 | budget-4 | mean regret | label rho |
|---|---:|---:|---:|---:|---:|---:|
| `selection_non_hard` | 0.416732 | 0.474267 | 0.392924 | 0.383006 | 0.0115776 | NA |
| `heldout_hard` | -0.38086 | -0.241418 | -0.803812 | -0.0973494 | 0.0581446 | 0.183678 |

## Verdict

Episode/depth transfer calibration selected on non-hard episodes does not improve hard perturbation-value allocation transfer.
