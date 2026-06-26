# Spectral-ablation hinge report

- Generated at: `2026-06-02T05:10:30.689978+00:00`
- Report schema id: `bedc-quality-lab:spectral-ablation-hinge-report`
- Envelope schema id: `bedc-quality-lab:evidence-envelope`
- Base rho by axis: `[0.92, 0.64]`
- Damp factor: `0.38`
- Envelope calls: `6`
- Ledger status: `open-or-partial`

## Hinge ledger

| rank | row | axes | spectral loss | orbit module | tail coupling | killed rho |
| ---: | --- | --- | ---: | --- | --- | --- |
| 1 | `single-axis` | `(0)` | 0.724180 | `axis-0-orbit` | `tail-sensitive` | `(0.349600, 0.640000)` |
| 2 | `single-axis` | `(1)` | 0.350454 | `axis-1-orbit` | `tail-sensitive` | `(0.920000, 0.243200)` |
| 3 | `module-analogue` | `(0, 1)` | 1.074634 | `full-latent-module` | `tail-sensitive` | `(0.349600, 0.243200)` |

## Arms

| arm | family | axes | mixing | degradation score | linear R2 delta | recovery error delta | quality_q delta |
| --- | --- | --- | --- | ---: | ---: | ---: | ---: |
| `vanilla` | `baseline` | `()` | `sinusoidal_shear` | 0.000000 | 0.000000 | 0.000000 | 0.000000 |
| `hinge-ranked-treatment` | `hinge-ranked-treatment` | `(0)` | `sinusoidal_shear` | 0.002496 | 0.000000 | 0.000000 | 0.002496 |
| `two-axis-module-analogue` | `hinge-ranked-treatment` | `(0, 1)` | `sinusoidal_shear` | -0.041664 | 0.000000 | 0.000000 | -0.041664 |
| `tail-mixing-perturbation` | `tail-mixing-perturbation` | `(0)` | `realnvp_coupling` | -0.360447 | -0.060238 | -0.127601 | -0.026688 |
| `matched-random-single-axis` | `matched-random-control` | `(1)` | `sinusoidal_shear` | 0.043382 | 0.010291 | 0.019357 | 0.046289 |
| `matched-random-module` | `matched-random-control` | `(1, 0)` | `sinusoidal_shear` | -0.244883 | -0.005621 | 0.006709 | -0.075715 |

## Rank correlation

- Spearman: `0.000000`
- Kendall: `0.000000`
- CI95: `[-1.000000, 1.000000]`
- Ordering note: observed metrics are read after arm execution and do not alter hinge ledger rank

## Negative-control audit

- Comparison: `hinge-ranked-treatment vs matched-random-control`
- Treatment score: `0.002496`
- Max control score: `0.043382`
- Treatment better than all controls: `False`
- Ledger status: `open-or-partial`

## Applicability boundary

- Claimed scope: `Gaussian 2D latent + diagonal Gaussian OU transition + runner-local hinge ledger.`
- Not claimed: This report does not claim full biological killed-walk coverage or formal BEDC closure.
