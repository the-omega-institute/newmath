# State-Generation Budget-Head Value Audit

- device: `cuda`
- selected epoch: `52`

| row | mean capture | budget-3 capture | budget-4 capture | mean regret |
|---|---:|---:|---:|---:|
| `budget_head_replacement` | -0.327145 | -0.419691 | 0.0958606 | 0.0522696 |

## Verdict

Budget-specific heads improve at least one stress statistic over pooled or single-budget baselines, but allocation closure remains open.
