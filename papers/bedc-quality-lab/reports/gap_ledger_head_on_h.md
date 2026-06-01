# Gap-Ledger Head on Learned h

- Generated at: `2026-06-01T20:47:16.842637+00:00`
- Representation boundary: `learned_h`
- Inference no ground-truth z: `true`
- Sample count: `384`
- Seed count: `30`
- Rho: `0.82`
- Gap channels: `prediction_error, low_margin, transition_unstable, off_target_intervention`
- Total records: `30`

## Arms

| arm | failure-detection AUROC | ECE | UnloggedErrorRate | critical unlogged error rate | prediction error rate |
| --- | ---: | ---: | ---: | ---: | ---: |
| `vanilla` | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) | 0.518261 +/- 0.050270 (95% CI +/- 0.017989) | 0.518261 +/- 0.050270 (95% CI +/- 0.017989) | 0.518261 +/- 0.050270 (95% CI +/- 0.017989) | 0.518261 +/- 0.050270 (95% CI +/- 0.017989) |
| `learned_gap_head_on_h` | 0.819193 +/- 0.044980 (95% CI +/- 0.016096) | 0.118070 +/- 0.028575 (95% CI +/- 0.010225) | 0.117391 +/- 0.054889 (95% CI +/- 0.019642) | 0.001449 +/- 0.004010 (95% CI +/- 0.001435) | 0.518261 +/- 0.050270 (95% CI +/- 0.017989) |

## Comparison

- UnloggedErrorRate delta learned minus vanilla: -0.400870 +/- 0.078919 (95% CI +/- 0.028241)
- Critical unlogged error rate delta learned minus vanilla: -0.516812 +/- 0.050119 (95% CI +/- 0.017935)
- Failure-detection AUROC delta learned minus vanilla: 0.319193 +/- 0.044980 (95% CI +/- 0.016096)

## Boundary

- Feature columns: `h:0, h:1, score:latent_x_positive, score:latent_y_positive, score:high_energy, margin:latent_x_positive, margin:latent_y_positive, margin:high_energy, transition_delta:latent_x_positive, transition_delta:latent_y_positive, transition_delta:high_energy, quality:quality_q, quality:quality_margin, quality:linear_identifiability_r2, quality:approx_identifiability_proxy`
- Forbidden inference columns: `z, z_pair, gap_label, prediction_error, eval_gap_labels`

## Gap Channels

- `prediction_error` (upstream_truth_diagnostic): At least one held-out h-trained distinction probe predicts the wrong truth label.
- `low_margin` (h_probe_margin): Minimum absolute h-probe margin is below a train-split quantile.
- `transition_unstable` (upstream_transition_truth): At least one distinction truth label differs under the OU pair.
- `off_target_intervention` (h_probe_intervention_diagnostic): A target intervention flips at least one non-target h-probe prediction.

## Negative Result Note

The learned h gap head reduced UnloggedErrorRate relative to vanilla under the predeclared protocol; thresholds and beta were not tuned after observing outcomes.

## Source Artifacts

- Generation script: `scripts/run_gap_ledger_head_on_h.py`
- Imported gap helper: `scripts/run_gaussian_ou_gap_ledger_head.py`
- JSON artifact: `reports/gap_ledger_head_on_h.json`
- Report artifact: `reports/gap_ledger_head_on_h.md`
- Import dependency chain:
  - `scripts/run_gap_ledger_head_on_h.py`
  - `scripts.run_gaussian_ou_gap_ledger_head`
  - `scripts.run_gaussian_ou_distinction_head`
  - `scripts.run_gaussian_ou_lejepa.run_experiment`
  - `bedc_quality_lab.toy_world.make_toy_batch`
  - `scripts.experiment_stats.metric_stats`

## Seed Order

`3787384488, 710762332, 4167120010, 1271555634, 614003796, 2194464496, 1717970438, 3479488918, 3184052640, 831661604, 717283106, 2840917146, 2907596428, 917320952, 1165058014, 3650807614, 4079602456, 2451442540, 3061295162, 1614193026, 2405103428, 1139059072, 2111027254, 1026040678, 2179066640, 1275137844, 2609221586, 1886350570, 3401492092, 2859678856`
