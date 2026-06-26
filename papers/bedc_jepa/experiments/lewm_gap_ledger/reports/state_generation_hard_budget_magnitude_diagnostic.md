# State-Generation Hard Budget-Magnitude Diagnostic

| slice | chosen-uniform | oracle-uniform | chosen-oracle | rho | pair acc | oracle match |
|---|---:|---:|---:|---:|---:|---:|
| `full` | 7.35549e-05 | -0.0241221 | 0.0241957 | 0.865732 | 0.997476 | 0.33123 |
| `non_hard` | -0.00623043 | -0.0210572 | 0.0148268 | 0.87316 | 0.997117 | 0.347748 |
| `hard_only` | 0.044361 | -0.0456543 | 0.0900153 | 0.824419 | 1 | 0.21519 |

## Hard-Slice Depth Counts

- chosen: `{'1': 12, '2': 20, '3': 20, '4': 10, '5': 17}`
- oracle: `{'1': 11, '2': 20, '3': 20, '4': 14, '5': 14}`

## Verdict

The hard-slice failure is not ordinary local option-error unreadability: hard-only score/error Spearman is high, non-hard allocation improves over uniform, but hard-only exact-budget allocation remains harmful.
