# State-Generation Oracle Budget Ceiling

| budget | hard observed | hard CI high | full observed | non-hard observed |
|---|---:|---:|---:|---:|
| `budget_2` | -0.0251242 | -0.0113884 | -0.0188416 | -0.0179253 |
| `budget_3` | -0.0429963 | -0.0230187 | -0.0247451 | -0.0220835 |
| `budget_4` | -0.0598596 | -0.0308812 | -0.0244541 | -0.0192909 |

## Verdict

Under the same exact episode-budget constraints, the oracle option-error score has hard-slice headroom at every tested budget magnitude. The allocation mechanism is therefore not vacuous; the current failure is a learned compute-value scoring boundary.
