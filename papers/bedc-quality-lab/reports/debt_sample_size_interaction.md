# Hidden-Debt Sample-Size Interaction Experiment

- Generated at: `2026-06-01T09:31:14.789178+00:00`
- Sample counts: `96, 192, 384, 768`
- Debt levels: `0.0, 0.1, 0.2, 0.3, 0.4`
- Seed count per cell: `15`
- Total records: `300`
- Interaction metric: `quality_q`

## Cell Error Bars

| sample_count | debt_level | mean +/- std | 95% CI half-width | 95% CI | n |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 96 | 0.0 | +0.741071 +/- 0.014019 | 0.007095 | [+0.733977, +0.748166] | 15 |
| 96 | 0.1 | +0.638892 +/- 0.017483 | 0.008847 | [+0.630045, +0.647740] | 15 |
| 96 | 0.2 | +0.620202 +/- 0.013176 | 0.006668 | [+0.613534, +0.626871] | 15 |
| 96 | 0.3 | +0.424970 +/- 0.022023 | 0.011145 | [+0.413825, +0.436115] | 15 |
| 96 | 0.4 | +0.326091 +/- 0.024993 | 0.012648 | [+0.313443, +0.338739] | 15 |
| 192 | 0.0 | +0.744781 +/- 0.013962 | 0.007066 | [+0.737715, +0.751846] | 15 |
| 192 | 0.1 | +0.640389 +/- 0.013655 | 0.006910 | [+0.633479, +0.647300] | 15 |
| 192 | 0.2 | +0.632684 +/- 0.018079 | 0.009149 | [+0.623535, +0.641833] | 15 |
| 192 | 0.3 | +0.426316 +/- 0.017592 | 0.008903 | [+0.417413, +0.435219] | 15 |
| 192 | 0.4 | +0.339442 +/- 0.011943 | 0.006044 | [+0.333398, +0.345486] | 15 |
| 384 | 0.0 | +0.747606 +/- 0.008065 | 0.004081 | [+0.743525, +0.751688] | 15 |
| 384 | 0.1 | +0.645347 +/- 0.009696 | 0.004907 | [+0.640440, +0.650254] | 15 |
| 384 | 0.2 | +0.637499 +/- 0.008055 | 0.004077 | [+0.633422, +0.641575] | 15 |
| 384 | 0.3 | +0.427226 +/- 0.011697 | 0.005919 | [+0.421306, +0.433145] | 15 |
| 384 | 0.4 | +0.344855 +/- 0.010306 | 0.005215 | [+0.339640, +0.350070] | 15 |
| 768 | 0.0 | +0.848036 +/- 0.005957 | 0.003015 | [+0.845022, +0.851051] | 15 |
| 768 | 0.1 | +0.745787 +/- 0.004025 | 0.002037 | [+0.743750, +0.747824] | 15 |
| 768 | 0.2 | +0.738297 +/- 0.008329 | 0.004215 | [+0.734082, +0.742512] | 15 |
| 768 | 0.3 | +0.538967 +/- 0.008614 | 0.004359 | [+0.534608, +0.543326] | 15 |
| 768 | 0.4 | +0.444185 +/- 0.007323 | 0.003706 | [+0.440479, +0.447891] | 15 |

## Per-Sample Count Degradation Slopes

| sample_count | degradation slope | 95% CI | standard error | points | status |
| ---: | ---: | ---: | ---: | ---: | --- |
| 96 | -1.043883 | [-1.498986, -0.588781] | 0.143024 | 5 | `ok` |
| 192 | -1.024751 | [-1.522525, -0.526976] | 0.156434 | 5 | `ok` |
| 384 | -1.023624 | [-1.530778, -0.516471] | 0.159382 | 5 | `ok` |
| 768 | -1.014523 | [-1.504054, -0.524992] | 0.153844 | 5 | `ok` |

## Interaction Test

- H0: per-sample_count degradation slope 95% confidence intervals share a common overlap.
- Common CI overlap: `true` with interval `[-1.498986, -0.588781]`
- H0 not rejected: `true`
- H0 rejected: `false`
- Negative result note: The experiment reports the measured CI-overlap outcome directly; no debt-level, sample-count, or seed setting is tuned after observing the result.

## Applicability Boundary

- Admitted family: Gaussian-OU toy world with lab-local hidden-debt assessment.
- Model: Deterministic standardized linear reader over synthetic Gaussian-OU samples.
- Sample count range: `96` to `768`.
- Sample counts: `96, 192, 384, 768`.
- Debt set: `0.0, 0.1, 0.2, 0.3, 0.4`.
- Seed count per cell: `15`.
- Metric behavior range: Reported only for finite measured quality_q values produced by the debt, metric, and ledger path; slope fitting fails closed for non-finite values, constant grids, or insufficient points.
- Claim scope: The interaction result applies only to the listed Gaussian-OU family, model, sample-count grid, debt grid, seed schedule, and quality_q construction.

## Source Artifacts

- Generation script: `scripts/run_debt_sample_size_interaction.py`
- Shared stats helper: `scripts/experiment_stats.py`
- Debt-dose helper: `scripts/run_debt_dose_response.py`
- JSON artifact: `reports/debt_sample_size_interaction.json`
- Report artifact: `reports/debt_sample_size_interaction.md`
- Import dependency chain:
  - `scripts/run_debt_sample_size_interaction.py`
  - `scripts.run_debt_dose_response._synthetic_metrics`
  - `bedc_quality_lab.metrics.metric_bundle`
  - `bedc_quality_lab.metrics.classifier_certificate`
  - `bedc_quality_lab.metrics.quality_components`
  - `bedc_quality_lab.debt.assess_debt`
  - `bedc_quality_lab.ledger.derive_ledger_gaps`
  - `bedc_quality_lab.scope.Scope`
  - `scripts.experiment_stats`

## Raw Record Index

| sample_count | debt_level | seed_index | seed | run_id | quality_q | source_artifacts |
| ---: | ---: | ---: | ---: | --- | ---: | --- |
| 96 | 0.0 | 0 | 1658793369 | `debt-sample-size-n96-debt-0p0-seed-1658793369` | +0.751582 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 1 | 1064191211 | `debt-sample-size-n96-debt-0p0-seed-1064191211` | +0.725947 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 2 | 1585309095 | `debt-sample-size-n96-debt-0p0-seed-1585309095` | +0.750302 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 3 | 1967181288 | `debt-sample-size-n96-debt-0p0-seed-1967181288` | +0.760015 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 4 | 3558308174 | `debt-sample-size-n96-debt-0p0-seed-3558308174` | +0.727214 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 5 | 4254153647 | `debt-sample-size-n96-debt-0p0-seed-4254153647` | +0.745649 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 6 | 918556631 | `debt-sample-size-n96-debt-0p0-seed-918556631` | +0.733008 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 7 | 242520713 | `debt-sample-size-n96-debt-0p0-seed-242520713` | +0.754383 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 8 | 2134344113 | `debt-sample-size-n96-debt-0p0-seed-2134344113` | +0.729149 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 9 | 3531915355 | `debt-sample-size-n96-debt-0p0-seed-3531915355` | +0.757660 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 10 | 1095114672 | `debt-sample-size-n96-debt-0p0-seed-1095114672` | +0.743993 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 11 | 1449565197 | `debt-sample-size-n96-debt-0p0-seed-1449565197` | +0.755455 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 12 | 3240137049 | `debt-sample-size-n96-debt-0p0-seed-3240137049` | +0.734048 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 13 | 3232995850 | `debt-sample-size-n96-debt-0p0-seed-3232995850` | +0.712959 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.0 | 14 | 2494328704 | `debt-sample-size-n96-debt-0p0-seed-2494328704` | +0.734704 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 0 | 170744623 | `debt-sample-size-n96-debt-0p1-seed-170744623` | +0.637551 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 1 | 1957712208 | `debt-sample-size-n96-debt-0p1-seed-1957712208` | +0.614277 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 2 | 1028755772 | `debt-sample-size-n96-debt-0p1-seed-1028755772` | +0.655697 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 3 | 3580845525 | `debt-sample-size-n96-debt-0p1-seed-3580845525` | +0.636448 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 4 | 3751600088 | `debt-sample-size-n96-debt-0p1-seed-3751600088` | +0.658414 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 5 | 3718336100 | `debt-sample-size-n96-debt-0p1-seed-3718336100` | +0.653880 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 6 | 3559760038 | `debt-sample-size-n96-debt-0p1-seed-3559760038` | +0.627045 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 7 | 4271159413 | `debt-sample-size-n96-debt-0p1-seed-4271159413` | +0.649098 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 8 | 1310860742 | `debt-sample-size-n96-debt-0p1-seed-1310860742` | +0.630845 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 9 | 52104642 | `debt-sample-size-n96-debt-0p1-seed-52104642` | +0.648582 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 10 | 3654698906 | `debt-sample-size-n96-debt-0p1-seed-3654698906` | +0.631716 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 11 | 1342150240 | `debt-sample-size-n96-debt-0p1-seed-1342150240` | +0.595130 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 12 | 2184565933 | `debt-sample-size-n96-debt-0p1-seed-2184565933` | +0.639204 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 13 | 3065046160 | `debt-sample-size-n96-debt-0p1-seed-3065046160` | +0.656164 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.1 | 14 | 3504009037 | `debt-sample-size-n96-debt-0p1-seed-3504009037` | +0.649334 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 0 | 4275888101 | `debt-sample-size-n96-debt-0p2-seed-4275888101` | +0.626122 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 1 | 1216464383 | `debt-sample-size-n96-debt-0p2-seed-1216464383` | +0.609629 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 2 | 3200657718 | `debt-sample-size-n96-debt-0p2-seed-3200657718` | +0.598677 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 3 | 3529657746 | `debt-sample-size-n96-debt-0p2-seed-3529657746` | +0.623300 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 4 | 2612514920 | `debt-sample-size-n96-debt-0p2-seed-2612514920` | +0.644821 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 5 | 1178369870 | `debt-sample-size-n96-debt-0p2-seed-1178369870` | +0.609452 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 6 | 3891026545 | `debt-sample-size-n96-debt-0p2-seed-3891026545` | +0.619693 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 7 | 64458975 | `debt-sample-size-n96-debt-0p2-seed-64458975` | +0.633455 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 8 | 2685399111 | `debt-sample-size-n96-debt-0p2-seed-2685399111` | +0.625353 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 9 | 2391879109 | `debt-sample-size-n96-debt-0p2-seed-2391879109` | +0.602961 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 10 | 2081526387 | `debt-sample-size-n96-debt-0p2-seed-2081526387` | +0.616220 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 11 | 3472181690 | `debt-sample-size-n96-debt-0p2-seed-3472181690` | +0.634126 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 12 | 3063426405 | `debt-sample-size-n96-debt-0p2-seed-3063426405` | +0.608089 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 13 | 3698884626 | `debt-sample-size-n96-debt-0p2-seed-3698884626` | +0.634934 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.2 | 14 | 2081909836 | `debt-sample-size-n96-debt-0p2-seed-2081909836` | +0.616204 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 0 | 3761261355 | `debt-sample-size-n96-debt-0p3-seed-3761261355` | +0.423923 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 1 | 808461146 | `debt-sample-size-n96-debt-0p3-seed-808461146` | +0.435077 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 2 | 1787923223 | `debt-sample-size-n96-debt-0p3-seed-1787923223` | +0.407836 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 3 | 1372113788 | `debt-sample-size-n96-debt-0p3-seed-1372113788` | +0.445322 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 4 | 3465409350 | `debt-sample-size-n96-debt-0p3-seed-3465409350` | +0.436323 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 5 | 156841013 | `debt-sample-size-n96-debt-0p3-seed-156841013` | +0.425383 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 6 | 3797921771 | `debt-sample-size-n96-debt-0p3-seed-3797921771` | +0.430935 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 7 | 2521081274 | `debt-sample-size-n96-debt-0p3-seed-2521081274` | +0.453355 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 8 | 3448621206 | `debt-sample-size-n96-debt-0p3-seed-3448621206` | +0.368598 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 9 | 2683478910 | `debt-sample-size-n96-debt-0p3-seed-2683478910` | +0.426564 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 10 | 2759222293 | `debt-sample-size-n96-debt-0p3-seed-2759222293` | +0.426443 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 11 | 3466703079 | `debt-sample-size-n96-debt-0p3-seed-3466703079` | +0.427645 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 12 | 2476684524 | `debt-sample-size-n96-debt-0p3-seed-2476684524` | +0.453496 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 13 | 2157006234 | `debt-sample-size-n96-debt-0p3-seed-2157006234` | +0.393656 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.3 | 14 | 2297113362 | `debt-sample-size-n96-debt-0p3-seed-2297113362` | +0.419993 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 0 | 3192497715 | `debt-sample-size-n96-debt-0p4-seed-3192497715` | +0.350672 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 1 | 366353580 | `debt-sample-size-n96-debt-0p4-seed-366353580` | +0.304896 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 2 | 1765978520 | `debt-sample-size-n96-debt-0p4-seed-1765978520` | +0.329144 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 3 | 2224971442 | `debt-sample-size-n96-debt-0p4-seed-2224971442` | +0.344699 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 4 | 2541160574 | `debt-sample-size-n96-debt-0p4-seed-2541160574` | +0.324104 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 5 | 3744062593 | `debt-sample-size-n96-debt-0p4-seed-3744062593` | +0.340049 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 6 | 1420085052 | `debt-sample-size-n96-debt-0p4-seed-1420085052` | +0.354014 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 7 | 1939314957 | `debt-sample-size-n96-debt-0p4-seed-1939314957` | +0.342711 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 8 | 2853538916 | `debt-sample-size-n96-debt-0p4-seed-2853538916` | +0.331632 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 9 | 4145247589 | `debt-sample-size-n96-debt-0p4-seed-4145247589` | +0.293931 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 10 | 4079478109 | `debt-sample-size-n96-debt-0p4-seed-4079478109` | +0.330082 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 11 | 1865074657 | `debt-sample-size-n96-debt-0p4-seed-1865074657` | +0.309265 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 12 | 641001069 | `debt-sample-size-n96-debt-0p4-seed-641001069` | +0.261772 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 13 | 2524004777 | `debt-sample-size-n96-debt-0p4-seed-2524004777` | +0.324279 | `scripts/run_debt_sample_size_interaction.py` |
| 96 | 0.4 | 14 | 3030231971 | `debt-sample-size-n96-debt-0p4-seed-3030231971` | +0.350109 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 0 | 2969010331 | `debt-sample-size-n192-debt-0p0-seed-2969010331` | +0.747664 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 1 | 2759631088 | `debt-sample-size-n192-debt-0p0-seed-2759631088` | +0.717910 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 2 | 1628041133 | `debt-sample-size-n192-debt-0p0-seed-1628041133` | +0.761073 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 3 | 1893693248 | `debt-sample-size-n192-debt-0p0-seed-1893693248` | +0.759468 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 4 | 3146779060 | `debt-sample-size-n192-debt-0p0-seed-3146779060` | +0.750423 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 5 | 1193346992 | `debt-sample-size-n192-debt-0p0-seed-1193346992` | +0.735823 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 6 | 1587661908 | `debt-sample-size-n192-debt-0p0-seed-1587661908` | +0.755867 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 7 | 2705605538 | `debt-sample-size-n192-debt-0p0-seed-2705605538` | +0.735708 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 8 | 1436853016 | `debt-sample-size-n192-debt-0p0-seed-1436853016` | +0.758684 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 9 | 4201684984 | `debt-sample-size-n192-debt-0p0-seed-4201684984` | +0.731525 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 10 | 151547421 | `debt-sample-size-n192-debt-0p0-seed-151547421` | +0.759280 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 11 | 2782998922 | `debt-sample-size-n192-debt-0p0-seed-2782998922` | +0.744564 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 12 | 1279683255 | `debt-sample-size-n192-debt-0p0-seed-1279683255` | +0.725080 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 13 | 2908343501 | `debt-sample-size-n192-debt-0p0-seed-2908343501` | +0.733540 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.0 | 14 | 2293312959 | `debt-sample-size-n192-debt-0p0-seed-2293312959` | +0.755098 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 0 | 1108422025 | `debt-sample-size-n192-debt-0p1-seed-1108422025` | +0.648162 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 1 | 735298831 | `debt-sample-size-n192-debt-0p1-seed-735298831` | +0.634217 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 2 | 3540570982 | `debt-sample-size-n192-debt-0p1-seed-3540570982` | +0.655172 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 3 | 1123860639 | `debt-sample-size-n192-debt-0p1-seed-1123860639` | +0.638080 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 4 | 1721078026 | `debt-sample-size-n192-debt-0p1-seed-1721078026` | +0.642342 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 5 | 2846955581 | `debt-sample-size-n192-debt-0p1-seed-2846955581` | +0.623844 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 6 | 480392281 | `debt-sample-size-n192-debt-0p1-seed-480392281` | +0.650349 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 7 | 975206016 | `debt-sample-size-n192-debt-0p1-seed-975206016` | +0.636533 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 8 | 109216855 | `debt-sample-size-n192-debt-0p1-seed-109216855` | +0.632622 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 9 | 3496992261 | `debt-sample-size-n192-debt-0p1-seed-3496992261` | +0.645360 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 10 | 421552829 | `debt-sample-size-n192-debt-0p1-seed-421552829` | +0.660551 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 11 | 137871657 | `debt-sample-size-n192-debt-0p1-seed-137871657` | +0.620305 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 12 | 3570316866 | `debt-sample-size-n192-debt-0p1-seed-3570316866` | +0.613698 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 13 | 94655862 | `debt-sample-size-n192-debt-0p1-seed-94655862` | +0.650676 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.1 | 14 | 467634645 | `debt-sample-size-n192-debt-0p1-seed-467634645` | +0.653929 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 0 | 501440123 | `debt-sample-size-n192-debt-0p2-seed-501440123` | +0.635866 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 1 | 4156572954 | `debt-sample-size-n192-debt-0p2-seed-4156572954` | +0.641676 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 2 | 3828005935 | `debt-sample-size-n192-debt-0p2-seed-3828005935` | +0.577443 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 3 | 733610516 | `debt-sample-size-n192-debt-0p2-seed-733610516` | +0.621122 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 4 | 3288877468 | `debt-sample-size-n192-debt-0p2-seed-3288877468` | +0.641703 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 5 | 626137116 | `debt-sample-size-n192-debt-0p2-seed-626137116` | +0.654954 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 6 | 2600766865 | `debt-sample-size-n192-debt-0p2-seed-2600766865` | +0.627263 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 7 | 3666811942 | `debt-sample-size-n192-debt-0p2-seed-3666811942` | +0.644433 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 8 | 2281979091 | `debt-sample-size-n192-debt-0p2-seed-2281979091` | +0.637792 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 9 | 403806839 | `debt-sample-size-n192-debt-0p2-seed-403806839` | +0.635688 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 10 | 1889342828 | `debt-sample-size-n192-debt-0p2-seed-1889342828` | +0.616122 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 11 | 575673435 | `debt-sample-size-n192-debt-0p2-seed-575673435` | +0.632302 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 12 | 4274783323 | `debt-sample-size-n192-debt-0p2-seed-4274783323` | +0.637582 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 13 | 1341160840 | `debt-sample-size-n192-debt-0p2-seed-1341160840` | +0.644061 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.2 | 14 | 3452689508 | `debt-sample-size-n192-debt-0p2-seed-3452689508` | +0.642258 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 0 | 1350660156 | `debt-sample-size-n192-debt-0p3-seed-1350660156` | +0.429279 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 1 | 3455037742 | `debt-sample-size-n192-debt-0p3-seed-3455037742` | +0.402953 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 2 | 2055369663 | `debt-sample-size-n192-debt-0p3-seed-2055369663` | +0.451487 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 3 | 3237989545 | `debt-sample-size-n192-debt-0p3-seed-3237989545` | +0.430776 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 4 | 2276436455 | `debt-sample-size-n192-debt-0p3-seed-2276436455` | +0.449057 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 5 | 171085224 | `debt-sample-size-n192-debt-0p3-seed-171085224` | +0.415987 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 6 | 563318961 | `debt-sample-size-n192-debt-0p3-seed-563318961` | +0.437119 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 7 | 4226708860 | `debt-sample-size-n192-debt-0p3-seed-4226708860` | +0.442238 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 8 | 93037377 | `debt-sample-size-n192-debt-0p3-seed-93037377` | +0.394256 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 9 | 4110694842 | `debt-sample-size-n192-debt-0p3-seed-4110694842` | +0.400504 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 10 | 4226247565 | `debt-sample-size-n192-debt-0p3-seed-4226247565` | +0.436690 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 11 | 722412759 | `debt-sample-size-n192-debt-0p3-seed-722412759` | +0.410826 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 12 | 1362744918 | `debt-sample-size-n192-debt-0p3-seed-1362744918` | +0.428432 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 13 | 4020054078 | `debt-sample-size-n192-debt-0p3-seed-4020054078` | +0.434310 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.3 | 14 | 2494396070 | `debt-sample-size-n192-debt-0p3-seed-2494396070` | +0.430826 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 0 | 1739810043 | `debt-sample-size-n192-debt-0p4-seed-1739810043` | +0.341598 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 1 | 2124287271 | `debt-sample-size-n192-debt-0p4-seed-2124287271` | +0.330734 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 2 | 2306724145 | `debt-sample-size-n192-debt-0p4-seed-2306724145` | +0.349977 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 3 | 176566474 | `debt-sample-size-n192-debt-0p4-seed-176566474` | +0.347546 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 4 | 474941205 | `debt-sample-size-n192-debt-0p4-seed-474941205` | +0.348759 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 5 | 3327780056 | `debt-sample-size-n192-debt-0p4-seed-3327780056` | +0.327947 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 6 | 1837079433 | `debt-sample-size-n192-debt-0p4-seed-1837079433` | +0.330036 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 7 | 489622173 | `debt-sample-size-n192-debt-0p4-seed-489622173` | +0.349019 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 8 | 1176055525 | `debt-sample-size-n192-debt-0p4-seed-1176055525` | +0.321025 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 9 | 3324108413 | `debt-sample-size-n192-debt-0p4-seed-3324108413` | +0.350232 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 10 | 1207778279 | `debt-sample-size-n192-debt-0p4-seed-1207778279` | +0.353267 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 11 | 3734514456 | `debt-sample-size-n192-debt-0p4-seed-3734514456` | +0.344151 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 12 | 2968928664 | `debt-sample-size-n192-debt-0p4-seed-2968928664` | +0.341113 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 13 | 740915679 | `debt-sample-size-n192-debt-0p4-seed-740915679` | +0.313755 | `scripts/run_debt_sample_size_interaction.py` |
| 192 | 0.4 | 14 | 3040961988 | `debt-sample-size-n192-debt-0p4-seed-3040961988` | +0.342469 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 0 | 2822916625 | `debt-sample-size-n384-debt-0p0-seed-2822916625` | +0.760609 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 1 | 2440648818 | `debt-sample-size-n384-debt-0p0-seed-2440648818` | +0.742715 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 2 | 4168288696 | `debt-sample-size-n384-debt-0p0-seed-4168288696` | +0.744984 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 3 | 2064742423 | `debt-sample-size-n384-debt-0p0-seed-2064742423` | +0.743079 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 4 | 361240054 | `debt-sample-size-n384-debt-0p0-seed-361240054` | +0.737805 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 5 | 1711718731 | `debt-sample-size-n384-debt-0p0-seed-1711718731` | +0.756577 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 6 | 325099245 | `debt-sample-size-n384-debt-0p0-seed-325099245` | +0.749715 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 7 | 1432886520 | `debt-sample-size-n384-debt-0p0-seed-1432886520` | +0.746149 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 8 | 2331104410 | `debt-sample-size-n384-debt-0p0-seed-2331104410` | +0.737613 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 9 | 4258633297 | `debt-sample-size-n384-debt-0p0-seed-4258633297` | +0.747297 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 10 | 3562313982 | `debt-sample-size-n384-debt-0p0-seed-3562313982` | +0.747898 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 11 | 1411441374 | `debt-sample-size-n384-debt-0p0-seed-1411441374` | +0.743001 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 12 | 118320539 | `debt-sample-size-n384-debt-0p0-seed-118320539` | +0.757632 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 13 | 2957190395 | `debt-sample-size-n384-debt-0p0-seed-2957190395` | +0.761303 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.0 | 14 | 3525859262 | `debt-sample-size-n384-debt-0p0-seed-3525859262` | +0.737717 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 0 | 3574400792 | `debt-sample-size-n384-debt-0p1-seed-3574400792` | +0.618930 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 1 | 1304339466 | `debt-sample-size-n384-debt-0p1-seed-1304339466` | +0.645633 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 2 | 2066096674 | `debt-sample-size-n384-debt-0p1-seed-2066096674` | +0.650901 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 3 | 4081934087 | `debt-sample-size-n384-debt-0p1-seed-4081934087` | +0.650133 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 4 | 3988015373 | `debt-sample-size-n384-debt-0p1-seed-3988015373` | +0.646172 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 5 | 143760572 | `debt-sample-size-n384-debt-0p1-seed-143760572` | +0.645862 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 6 | 2394342585 | `debt-sample-size-n384-debt-0p1-seed-2394342585` | +0.648250 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 7 | 2381649393 | `debt-sample-size-n384-debt-0p1-seed-2381649393` | +0.638933 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 8 | 3180822 | `debt-sample-size-n384-debt-0p1-seed-3180822` | +0.629159 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 9 | 3666002552 | `debt-sample-size-n384-debt-0p1-seed-3666002552` | +0.648538 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 10 | 3875750224 | `debt-sample-size-n384-debt-0p1-seed-3875750224` | +0.648295 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 11 | 1517736805 | `debt-sample-size-n384-debt-0p1-seed-1517736805` | +0.648849 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 12 | 2224857056 | `debt-sample-size-n384-debt-0p1-seed-2224857056` | +0.650546 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 13 | 1479794592 | `debt-sample-size-n384-debt-0p1-seed-1479794592` | +0.656922 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.1 | 14 | 2619881999 | `debt-sample-size-n384-debt-0p1-seed-2619881999` | +0.653085 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 0 | 2081940462 | `debt-sample-size-n384-debt-0p2-seed-2081940462` | +0.632248 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 1 | 2199941718 | `debt-sample-size-n384-debt-0p2-seed-2199941718` | +0.652267 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 2 | 864810693 | `debt-sample-size-n384-debt-0p2-seed-864810693` | +0.637468 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 3 | 3723572942 | `debt-sample-size-n384-debt-0p2-seed-3723572942` | +0.634882 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 4 | 1149786542 | `debt-sample-size-n384-debt-0p2-seed-1149786542` | +0.633093 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 5 | 1151225895 | `debt-sample-size-n384-debt-0p2-seed-1151225895` | +0.622069 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 6 | 3814320469 | `debt-sample-size-n384-debt-0p2-seed-3814320469` | +0.643777 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 7 | 475313245 | `debt-sample-size-n384-debt-0p2-seed-475313245` | +0.649681 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 8 | 63922644 | `debt-sample-size-n384-debt-0p2-seed-63922644` | +0.640574 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 9 | 1823082824 | `debt-sample-size-n384-debt-0p2-seed-1823082824` | +0.644837 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 10 | 2417036177 | `debt-sample-size-n384-debt-0p2-seed-2417036177` | +0.640147 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 11 | 4022257757 | `debt-sample-size-n384-debt-0p2-seed-4022257757` | +0.626543 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 12 | 1672199271 | `debt-sample-size-n384-debt-0p2-seed-1672199271` | +0.635112 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 13 | 1156721206 | `debt-sample-size-n384-debt-0p2-seed-1156721206` | +0.635583 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.2 | 14 | 1294022263 | `debt-sample-size-n384-debt-0p2-seed-1294022263` | +0.634195 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 0 | 3677719028 | `debt-sample-size-n384-debt-0p3-seed-3677719028` | +0.419884 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 1 | 2538887005 | `debt-sample-size-n384-debt-0p3-seed-2538887005` | +0.419611 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 2 | 1596626707 | `debt-sample-size-n384-debt-0p3-seed-1596626707` | +0.422892 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 3 | 3657408163 | `debt-sample-size-n384-debt-0p3-seed-3657408163` | +0.434011 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 4 | 62981801 | `debt-sample-size-n384-debt-0p3-seed-62981801` | +0.425204 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 5 | 4206250932 | `debt-sample-size-n384-debt-0p3-seed-4206250932` | +0.432449 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 6 | 1506758716 | `debt-sample-size-n384-debt-0p3-seed-1506758716` | +0.448788 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 7 | 933145570 | `debt-sample-size-n384-debt-0p3-seed-933145570` | +0.418340 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 8 | 941226287 | `debt-sample-size-n384-debt-0p3-seed-941226287` | +0.398757 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 9 | 1328100032 | `debt-sample-size-n384-debt-0p3-seed-1328100032` | +0.430406 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 10 | 1582016036 | `debt-sample-size-n384-debt-0p3-seed-1582016036` | +0.422518 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 11 | 3433532927 | `debt-sample-size-n384-debt-0p3-seed-3433532927` | +0.431363 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 12 | 3663596269 | `debt-sample-size-n384-debt-0p3-seed-3663596269` | +0.425871 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 13 | 2575231279 | `debt-sample-size-n384-debt-0p3-seed-2575231279` | +0.436186 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.3 | 14 | 557113210 | `debt-sample-size-n384-debt-0p3-seed-557113210` | +0.442105 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 0 | 4176099203 | `debt-sample-size-n384-debt-0p4-seed-4176099203` | +0.346011 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 1 | 1936377642 | `debt-sample-size-n384-debt-0p4-seed-1936377642` | +0.341964 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 2 | 1205601793 | `debt-sample-size-n384-debt-0p4-seed-1205601793` | +0.354459 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 3 | 539627094 | `debt-sample-size-n384-debt-0p4-seed-539627094` | +0.339876 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 4 | 847086749 | `debt-sample-size-n384-debt-0p4-seed-847086749` | +0.346841 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 5 | 1217193321 | `debt-sample-size-n384-debt-0p4-seed-1217193321` | +0.354506 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 6 | 3666386271 | `debt-sample-size-n384-debt-0p4-seed-3666386271` | +0.326822 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 7 | 1813524101 | `debt-sample-size-n384-debt-0p4-seed-1813524101` | +0.338207 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 8 | 2312453650 | `debt-sample-size-n384-debt-0p4-seed-2312453650` | +0.351368 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 9 | 2678772953 | `debt-sample-size-n384-debt-0p4-seed-2678772953` | +0.359095 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 10 | 4046114288 | `debt-sample-size-n384-debt-0p4-seed-4046114288` | +0.333091 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 11 | 3737395760 | `debt-sample-size-n384-debt-0p4-seed-3737395760` | +0.352476 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 12 | 1335333088 | `debt-sample-size-n384-debt-0p4-seed-1335333088` | +0.325618 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 13 | 609405152 | `debt-sample-size-n384-debt-0p4-seed-609405152` | +0.350812 | `scripts/run_debt_sample_size_interaction.py` |
| 384 | 0.4 | 14 | 156368405 | `debt-sample-size-n384-debt-0p4-seed-156368405` | +0.351676 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 0 | 2260650966 | `debt-sample-size-n768-debt-0p0-seed-2260650966` | +0.850523 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 1 | 3482713506 | `debt-sample-size-n768-debt-0p0-seed-3482713506` | +0.845607 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 2 | 3649248936 | `debt-sample-size-n768-debt-0p0-seed-3649248936` | +0.846992 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 3 | 1899149790 | `debt-sample-size-n768-debt-0p0-seed-1899149790` | +0.854421 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 4 | 689937145 | `debt-sample-size-n768-debt-0p0-seed-689937145` | +0.837576 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 5 | 528176977 | `debt-sample-size-n768-debt-0p0-seed-528176977` | +0.848360 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 6 | 146955048 | `debt-sample-size-n768-debt-0p0-seed-146955048` | +0.850031 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 7 | 2548720873 | `debt-sample-size-n768-debt-0p0-seed-2548720873` | +0.848758 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 8 | 1507843777 | `debt-sample-size-n768-debt-0p0-seed-1507843777` | +0.856581 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 9 | 1361453474 | `debt-sample-size-n768-debt-0p0-seed-1361453474` | +0.854116 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 10 | 2188492189 | `debt-sample-size-n768-debt-0p0-seed-2188492189` | +0.840684 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 11 | 1462893591 | `debt-sample-size-n768-debt-0p0-seed-1462893591` | +0.853097 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 12 | 1309191473 | `debt-sample-size-n768-debt-0p0-seed-1309191473` | +0.849652 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 13 | 265879521 | `debt-sample-size-n768-debt-0p0-seed-265879521` | +0.847798 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.0 | 14 | 3263805732 | `debt-sample-size-n768-debt-0p0-seed-3263805732` | +0.836350 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 0 | 2723474065 | `debt-sample-size-n768-debt-0p1-seed-2723474065` | +0.749229 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 1 | 4036502478 | `debt-sample-size-n768-debt-0p1-seed-4036502478` | +0.750142 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 2 | 445045889 | `debt-sample-size-n768-debt-0p1-seed-445045889` | +0.739938 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 3 | 2648854166 | `debt-sample-size-n768-debt-0p1-seed-2648854166` | +0.744488 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 4 | 2667781301 | `debt-sample-size-n768-debt-0p1-seed-2667781301` | +0.747703 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 5 | 598280628 | `debt-sample-size-n768-debt-0p1-seed-598280628` | +0.750118 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 6 | 392388046 | `debt-sample-size-n768-debt-0p1-seed-392388046` | +0.747364 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 7 | 1497110416 | `debt-sample-size-n768-debt-0p1-seed-1497110416` | +0.746247 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 8 | 3869804444 | `debt-sample-size-n768-debt-0p1-seed-3869804444` | +0.749757 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 9 | 4010627732 | `debt-sample-size-n768-debt-0p1-seed-4010627732` | +0.745423 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 10 | 3075413119 | `debt-sample-size-n768-debt-0p1-seed-3075413119` | +0.749658 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 11 | 2265162957 | `debt-sample-size-n768-debt-0p1-seed-2265162957` | +0.745305 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 12 | 4062182259 | `debt-sample-size-n768-debt-0p1-seed-4062182259` | +0.740939 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 13 | 2700703256 | `debt-sample-size-n768-debt-0p1-seed-2700703256` | +0.743322 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.1 | 14 | 3646649870 | `debt-sample-size-n768-debt-0p1-seed-3646649870` | +0.737170 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 0 | 3944988358 | `debt-sample-size-n768-debt-0p2-seed-3944988358` | +0.737043 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 1 | 2411650142 | `debt-sample-size-n768-debt-0p2-seed-2411650142` | +0.739403 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 2 | 1788501161 | `debt-sample-size-n768-debt-0p2-seed-1788501161` | +0.729039 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 3 | 284936065 | `debt-sample-size-n768-debt-0p2-seed-284936065` | +0.747601 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 4 | 619790489 | `debt-sample-size-n768-debt-0p2-seed-619790489` | +0.735998 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 5 | 635758531 | `debt-sample-size-n768-debt-0p2-seed-635758531` | +0.726674 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 6 | 1147376595 | `debt-sample-size-n768-debt-0p2-seed-1147376595` | +0.748480 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 7 | 175942844 | `debt-sample-size-n768-debt-0p2-seed-175942844` | +0.752870 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 8 | 3008197284 | `debt-sample-size-n768-debt-0p2-seed-3008197284` | +0.744135 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 9 | 434879543 | `debt-sample-size-n768-debt-0p2-seed-434879543` | +0.744598 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 10 | 1334524096 | `debt-sample-size-n768-debt-0p2-seed-1334524096` | +0.739846 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 11 | 1933396001 | `debt-sample-size-n768-debt-0p2-seed-1933396001` | +0.725228 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 12 | 3105018677 | `debt-sample-size-n768-debt-0p2-seed-3105018677` | +0.737388 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 13 | 3643959359 | `debt-sample-size-n768-debt-0p2-seed-3643959359` | +0.728753 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.2 | 14 | 3757636498 | `debt-sample-size-n768-debt-0p2-seed-3757636498` | +0.737401 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 0 | 260146141 | `debt-sample-size-n768-debt-0p3-seed-260146141` | +0.539996 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 1 | 3968503888 | `debt-sample-size-n768-debt-0p3-seed-3968503888` | +0.530893 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 2 | 409288390 | `debt-sample-size-n768-debt-0p3-seed-409288390` | +0.542239 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 3 | 3308301591 | `debt-sample-size-n768-debt-0p3-seed-3308301591` | +0.545941 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 4 | 520567776 | `debt-sample-size-n768-debt-0p3-seed-520567776` | +0.516512 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 5 | 1795516591 | `debt-sample-size-n768-debt-0p3-seed-1795516591` | +0.545402 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 6 | 3443899580 | `debt-sample-size-n768-debt-0p3-seed-3443899580` | +0.546600 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 7 | 3514871687 | `debt-sample-size-n768-debt-0p3-seed-3514871687` | +0.546728 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 8 | 3654560211 | `debt-sample-size-n768-debt-0p3-seed-3654560211` | +0.547360 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 9 | 1284550493 | `debt-sample-size-n768-debt-0p3-seed-1284550493` | +0.528275 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 10 | 161911140 | `debt-sample-size-n768-debt-0p3-seed-161911140` | +0.537276 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 11 | 1106790913 | `debt-sample-size-n768-debt-0p3-seed-1106790913` | +0.534461 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 12 | 172984221 | `debt-sample-size-n768-debt-0p3-seed-172984221` | +0.543232 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 13 | 2261067804 | `debt-sample-size-n768-debt-0p3-seed-2261067804` | +0.536512 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.3 | 14 | 995756842 | `debt-sample-size-n768-debt-0p3-seed-995756842` | +0.543073 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 0 | 3246466745 | `debt-sample-size-n768-debt-0p4-seed-3246466745` | +0.437855 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 1 | 1628765852 | `debt-sample-size-n768-debt-0p4-seed-1628765852` | +0.438904 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 2 | 211873028 | `debt-sample-size-n768-debt-0p4-seed-211873028` | +0.440514 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 3 | 1327667229 | `debt-sample-size-n768-debt-0p4-seed-1327667229` | +0.444711 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 4 | 1393645489 | `debt-sample-size-n768-debt-0p4-seed-1393645489` | +0.451605 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 5 | 4148617006 | `debt-sample-size-n768-debt-0p4-seed-4148617006` | +0.448423 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 6 | 3463667726 | `debt-sample-size-n768-debt-0p4-seed-3463667726` | +0.451061 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 7 | 1873080990 | `debt-sample-size-n768-debt-0p4-seed-1873080990` | +0.443647 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 8 | 912111013 | `debt-sample-size-n768-debt-0p4-seed-912111013` | +0.452234 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 9 | 113809364 | `debt-sample-size-n768-debt-0p4-seed-113809364` | +0.449287 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 10 | 1397101314 | `debt-sample-size-n768-debt-0p4-seed-1397101314` | +0.429315 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 11 | 2754680139 | `debt-sample-size-n768-debt-0p4-seed-2754680139` | +0.444993 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 12 | 3255133243 | `debt-sample-size-n768-debt-0p4-seed-3255133243` | +0.430917 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 13 | 388215534 | `debt-sample-size-n768-debt-0p4-seed-388215534` | +0.449725 | `scripts/run_debt_sample_size_interaction.py` |
| 768 | 0.4 | 14 | 233972551 | `debt-sample-size-n768-debt-0p4-seed-233972551` | +0.449585 | `scripts/run_debt_sample_size_interaction.py` |
