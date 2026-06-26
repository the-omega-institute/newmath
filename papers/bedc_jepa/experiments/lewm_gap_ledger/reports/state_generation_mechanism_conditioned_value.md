# State-Generation Mechanism-Conditioned Value Audit

- device: `cuda`
- mechanism feature dim: `12`
- best mechanism row: `mechanism_uniform_relative_cost`
- best direct row: `uniform_relative_cost`

| row | mean capture | budget-3 capture | budget-4 capture | mean regret |
|---|---:|---:|---:|---:|
| `mechanism_uniform_relative_cost` | 0.111859 | 0.123374 | 0.096023 | 0.0380029 |
| `mechanism_option_error` | -0.183532 | -0.54674 | -0.151413 | 0.0522814 |

## Verdict

Mechanism-conditioned rollout features improve at least one direct oracle-value gap statistic, but the hard oracle-headroom boundary remains open.
