# State-Generation Direct Oracle-Value Audit

- device: `cuda`
- direct target count: `4`
- best direct row: `uniform_relative_cost`
- best existing candidate: `assignment_priority_residual`

| row | mean capture | budget-3 capture | budget-4 capture | mean regret |
|---|---:|---:|---:|---:|
| `uniform_relative_cost` | -0.198634 | -0.360982 | -0.128457 | 0.0512884 |
| `direct_option_error` | -0.752266 | -0.66213 | -0.226404 | 0.068126 |
| `tail_weighted_option_error` | -0.964215 | -0.734867 | -0.297118 | 0.0747032 |
| `oracle_relative_regret` | -1.00155 | -0.783764 | -0.218064 | 0.0750173 |

## Verdict

Direct option-conditioned oracle-value targets do not outperform the existing fixed-candidate pool on the hard oracle-headroom audit. The missing object remains a stronger option-conditioned compute-value mechanism, not another evaluation-time score selector.
