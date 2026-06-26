# Spectral-ablation discovery projection

- Source JSON artifact: `reports/spectral_ablation_hinge.json`
- Projection script: `scripts/run_spectral_ablation_discovery.py`

## Verdicts

| arm | family | degradation | surface delta | shift info | net | structural | positive | verdict |
| --- | --- | ---: | ---: | ---: | ---: | --- | --- | --- |
| `hinge-ranked-treatment` | `hinge-ranked-treatment` | 0.002496 | 2 | 2 | -0.042496 | `true` | `false` | `negative` |
| `two-axis-module-analogue` | `hinge-ranked-treatment` | -0.041664 | 2 | 2 | 0.001664 | `true` | `true` | `positive` |
| `tail-mixing-perturbation` | `tail-mixing-perturbation` | -0.360447 | 6 | 6 | 0.240447 | `true` | `true` | `positive` |
| `matched-random-single-axis` | `matched-random-control` | 0.043382 | 6 | 6 | -0.163382 | `true` | `false` | `negative` |
| `matched-random-module` | `matched-random-control` | -0.244883 | 6 | 6 | 0.124883 | `true` | `true` | `positive` |

## Rank Correlation

- Method: `hinge-observed-degradation-vs-discovery-net-information`
- Spearman: `-1.000000`
- Source hinge Spearman: `0.000000`

## Matched Random Baseline

- Treatment score: `0.002496`
- Max control score: `0.043382`
- Treatment better than all controls: `False`

## Applicability Boundary

- Claimed scope: `Gaussian 2D latent + diagonal Gaussian OU transition + runner-local hinge ledger.`
- Not claimed: This report does not claim full biological killed-walk coverage or formal BEDC closure.
