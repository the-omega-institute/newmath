# Gap-Ledger Head on Learned h

- Generated at: `2026-06-02T11:36:43.469111+00:00`
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
| `vanilla` | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) | 0.513043 +/- 0.050343 (95% CI +/- 0.018015) | 0.513043 +/- 0.050343 (95% CI +/- 0.018015) | 0.513043 +/- 0.050343 (95% CI +/- 0.018015) | 0.513043 +/- 0.050343 (95% CI +/- 0.018015) |
| `learned_gap_head_on_h` | 0.820217 +/- 0.047445 (95% CI +/- 0.016978) | 0.124272 +/- 0.026071 (95% CI +/- 0.009329) | 0.121739 +/- 0.062913 (95% CI +/- 0.022513) | 0.001159 +/- 0.003775 (95% CI +/- 0.001351) | 0.513043 +/- 0.050343 (95% CI +/- 0.018015) |
| `matched_random_gap_head` | 0.493823 +/- 0.097903 (95% CI +/- 0.035034) | 0.114396 +/- 0.050620 (95% CI +/- 0.018114) | 0.251594 +/- 0.092279 (95% CI +/- 0.033022) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.513043 +/- 0.050343 (95% CI +/- 0.018015) |

## Comparison

- UnloggedErrorRate delta learned minus vanilla: -0.391304 +/- 0.085627 (95% CI +/- 0.030641)
- Critical unlogged error rate delta learned minus vanilla: -0.511884 +/- 0.049860 (95% CI +/- 0.017842)
- Failure-detection AUROC delta learned minus vanilla: 0.320217 +/- 0.047445 (95% CI +/- 0.016978)
- UnloggedErrorRate delta matched-random minus vanilla: -0.261449 +/- 0.113422 (95% CI +/- 0.040588)
- Critical unlogged error rate delta matched-random minus vanilla: -0.513043 +/- 0.050343 (95% CI +/- 0.018015)
- Failure-detection AUROC delta matched-random minus vanilla: -0.006177 +/- 0.097903 (95% CI +/- 0.035034)

## Matched-Random Control

- Control arm: `matched_random_gap_head`
- Label protocol: `seed_deterministic_per_channel_permutation`
- Control positive: `false`
- Main claim status: `source_evidence_only`

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
- JSON artifact: `reports/canonical/gap-head-on-h.json`
- Report artifact: `reports/canonical/gap-head-on-h.md`
- Import dependency chain:
  - `scripts/run_gap_ledger_head_on_h.py`
  - `scripts.run_gaussian_ou_gap_ledger_head`
  - `scripts.run_gaussian_ou_distinction_head`
  - `scripts.run_gaussian_ou_lejepa.run_experiment`
  - `bedc_quality_lab.toy_world.make_toy_batch`
  - `scripts.experiment_stats.metric_stats`

## Seed Order

`3787384488, 710762332, 4167120010, 1271555634, 614003796, 2194464496, 1717970438, 3479488918, 3184052640, 831661604, 717283106, 2840917146, 2907596428, 917320952, 1165058014, 3650807614, 4079602456, 2451442540, 3061295162, 1614193026, 2405103428, 1139059072, 2111027254, 1026040678, 2179066640, 1275137844, 2609221586, 1886350570, 3401492092, 2859678856`
