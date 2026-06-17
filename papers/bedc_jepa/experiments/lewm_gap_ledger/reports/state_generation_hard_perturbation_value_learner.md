# State-Generation Hard Perturbation-Value Learner

- device: `cuda`
- mean hard label rho: `0.26347`
- fixed-score baseline rho: `0.171908`

| budget | label rho | capture | regret |
|---|---:|---:|---:|
| `budget_2` | 0.405166 | -0.155576 | 0.0290329 |
| `budget_3` | 0.121584 | 0.0787014 | 0.0396124 |
| `budget_4` | 0.263661 | -0.127488 | 0.067491 |

## Verdict

Perturbation-value supervision does not materially improve hard label alignment or hard exact-budget allocation capture in this learner.
