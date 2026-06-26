# Dose-response discovery projection

- Source JSON artifact: `reports/debt_dose_response.json`
- Projection script: `scripts/run_dose_response_discovery.py`
- Conclusion: `monotonic`

## Per-dose Verdicts

| dose | net information | surface delta | shift info | net positive | positive | verdict |
| ---: | ---: | ---: | ---: | --- | --- | --- |
| 0.0 | -0.030000 | 0 | 0 | `false` | `false` | `compression` |
| 0.1 | 0.110446 | 4 | 4 | `true` | `true` | `positive` |
| 0.2 | 0.506792 | 5 | 5 | `true` | `true` | `positive` |
| 0.3 | 0.708968 | 5 | 5 | `true` | `true` | `positive` |
| 0.4 | 0.904580 | 5 | 5 | `true` | `true` | `positive` |

## Rank Correlation

- Spearman: `1.000000`
- Kendall tau: `1.000000`

## Matched Random Baseline

- Seed: `53120260602`
- Permutations: `200`
- 95% absolute Spearman: `0.900000`
- Observed exceeds 95% baseline: `true`

## Applicability Boundary

- Claim scope: `Empirical monotonicity is claimed only for the generated Gaussian-OU toy world, the deterministic runner constants, and the listed debt grid.`
