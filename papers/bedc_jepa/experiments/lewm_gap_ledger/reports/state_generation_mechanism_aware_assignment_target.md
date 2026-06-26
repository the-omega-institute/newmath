# State-Generation Mechanism-Aware Assignment Target

- selected non-hard target: `mechanism_forced_delta`
- candidate count: `17`

| target | hard mean capture | hard budget-2 | hard budget-3 | hard budget-4 | hard regret | hard label rho |
|---|---:|---:|---:|---:|---:|---:|
| `selected` | 1 | 1 | 1 | 1 | 0 | 1 |
| `learner_base` | -0.0681208 | -0.155576 | 0.0787014 | -0.127488 | 0.0453788 | 0.26347 |
| `mechanism_forced_delta` | 1 | 1 | 1 | 1 | 0 | 1 |
| `oracle_option_error` | 1 | 1 | 1 | 1 | 0 | 0.314856 |

## Verdict

Mechanism-aware target selection transfers to hard episodes and improves over the base perturbation-value learner on this export; independent validation is required.
