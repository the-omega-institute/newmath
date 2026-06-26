# State-Generation Candidate Oracle Gap

- candidate count: `22`
- best candidate: `assignment_priority_residual`

| candidate | mean capture | budget-3 capture | budget-4 capture | mean regret |
|---|---:|---:|---:|---:|
| `assignment_priority_residual` | 0.0242164 | 0.121578 | -0.0629458 | 0.0420561 |
| `benefit_selector` | 0.0242164 | 0.121578 | -0.0629458 | 0.0420561 |
| `residual_priority` | 0.0242164 | 0.121578 | -0.0629458 | 0.0420561 |
| `assignment_raw_geometry` | -0.00199754 | 0.129296 | -0.151936 | 0.0436991 |
| `residual_raw` | -0.00199754 | 0.129296 | -0.151936 | 0.0436991 |
| `geometry_conditioned` | -0.139465 | -0.361481 | 0.100074 | 0.0471587 |
| `budget_priority` | -0.306564 | -0.393556 | -0.344062 | 0.0566905 |
| `geometry_regime_weighted` | -0.315768 | -0.416964 | -0.0803424 | 0.0540077 |
| `episode_dual_price` | -0.477534 | -1.16712 | -0.161263 | 0.0634778 |
| `regret_dual_price` | -0.477534 | -1.16712 | -0.161263 | 0.0634778 |
| `episode_assignment_value` | -0.550689 | -0.656143 | -0.030935 | 0.0607627 |
| `episode_seed_mean` | -0.553439 | -0.775014 | -0.188396 | 0.0633631 |

## Verdict

No existing learned candidate approaches the hard oracle budget ceiling. The candidate pool audit supports a new option-conditioned compute-value objective rather than more selection over existing score families.
