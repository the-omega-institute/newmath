# Gap-Ledger Head on Learned h

- Generated at: `2026-06-04T07:26:54.698218+00:00`
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
| `vanilla` | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) | 0.505797 +/- 0.054620 (95% CI +/- 0.019545) | 0.505797 +/- 0.054620 (95% CI +/- 0.019545) | 0.505797 +/- 0.054620 (95% CI +/- 0.019545) | 0.505797 +/- 0.054620 (95% CI +/- 0.019545) |
| `learned_gap_head_on_h` | 0.815589 +/- 0.044417 (95% CI +/- 0.015894) | 0.115027 +/- 0.029219 (95% CI +/- 0.010456) | 0.124928 +/- 0.063140 (95% CI +/- 0.022594) | 0.000580 +/- 0.002206 (95% CI +/- 0.000789) | 0.505797 +/- 0.054620 (95% CI +/- 0.019545) |
| `matched_random_gap_head` | 0.493183 +/- 0.096779 (95% CI +/- 0.034632) | 0.122031 +/- 0.048069 (95% CI +/- 0.017201) | 0.262899 +/- 0.086164 (95% CI +/- 0.030833) | 0.000000 +/- 0.000000 (95% CI +/- 0.000000) | 0.505797 +/- 0.054620 (95% CI +/- 0.019545) |

## Comparison

- UnloggedErrorRate delta learned minus vanilla: -0.380870 +/- 0.085639 (95% CI +/- 0.030646)
- Critical unlogged error rate delta learned minus vanilla: -0.505217 +/- 0.054537 (95% CI +/- 0.019516)
- Failure-detection AUROC delta learned minus vanilla: 0.315589 +/- 0.044417 (95% CI +/- 0.015894)
- UnloggedErrorRate delta matched-random minus vanilla: -0.242899 +/- 0.099825 (95% CI +/- 0.035722)
- Critical unlogged error rate delta matched-random minus vanilla: -0.505797 +/- 0.054620 (95% CI +/- 0.019545)
- Failure-detection AUROC delta matched-random minus vanilla: -0.006817 +/- 0.096779 (95% CI +/- 0.034632)

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
