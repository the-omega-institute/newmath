# State-Generation Budget Replacement-Value Audit

- device: `cuda`
- best replacement row: `replacement_budget4`
- best mechanism row: `mechanism_uniform_relative_cost`

| row | mean capture | budget-3 capture | budget-4 capture | mean regret |
|---|---:|---:|---:|---:|
| `replacement_budget4` | 0.126069 | 0.174094 | -0.0743724 | 0.0393166 |
| `replacement_budget2` | -0.146639 | -0.242423 | -0.125468 | 0.0492411 |
| `replacement_budget3` | -0.233444 | -0.29182 | -0.00440104 | 0.0503146 |

## Verdict

Budget-aware forced-replacement targets improve at least one hard oracle-gap statistic over passive mechanism-conditioned features, but allocation closure remains open.
