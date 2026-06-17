# State-Generation Learned Oracle Gap

| scorer | budget | score delta | oracle delta | regret | capture |
|---|---:|---:|---:|---:|---:|
| `benefit_selector` | `budget_2` | -0.000352168 | -0.0251242 | 0.024772 | 0.0140171 |
| `benefit_selector` | `budget_3` | -0.00522739 | -0.0429963 | 0.0377689 | 0.121578 |
| `benefit_selector` | `budget_4` | 0.00376791 | -0.0598596 | 0.0636275 | -0.0629458 |
| `priority_residual` | `budget_2` | -0.000352168 | -0.0251242 | 0.024772 | 0.0140171 |
| `priority_residual` | `budget_3` | -0.00522739 | -0.0429963 | 0.0377689 | 0.121578 |
| `priority_residual` | `budget_4` | 0.00376791 | -0.0598596 | 0.0636275 | -0.0629458 |
| `raw_geometry_option` | `budget_2` | -0.000418248 | -0.0251242 | 0.024706 | 0.0166472 |
| `raw_geometry_option` | `budget_3` | -0.00555924 | -0.0429963 | 0.037437 | 0.129296 |
| `raw_geometry_option` | `budget_4` | 0.00909481 | -0.0598596 | 0.0689544 | -0.151936 |

## Verdict

The learned scores remain far from the hard exact-budget oracle ceiling: budget-3 captures only a small fraction of oracle headroom and budget-four capture can reverse sign. The missing object is a learned option-conditioned compute-value score, not another scalar failure-rank transform.
