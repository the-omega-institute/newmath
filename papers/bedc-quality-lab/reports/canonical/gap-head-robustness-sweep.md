# Gap-Head Robustness Sweep

- Generated at: `2026-06-03T03:46:14.402062+00:00`
- Artifact: `bedc-quality-lab:gap-head-robustness-sweep`
- Final status: `pass`
- Final claim scope: `full_feature_family_gap_classifier`
- Claim: Gap classifiers can be learned on representations to reduce unlogged model errors.
- Elapsed seconds: `11.507995`

## A-HG Gates

| gate | status | criterion |
| --- | --- | --- |
| `A-HG1` | `pass` | learned AUROC ci95_low > matched-random AUROC ci95_high and learned AUROC mean >= 0.75 |
| `A-HG2` | `pass` | learned UnloggedErrorRate reduction ci95_low > matched-random reduction ci95_high and learned mean reduction > 0 |
| `A-HG3` | `pass` | producer control_verdict.positive is false and matched-random AUROC ci95_high <= 0.6 |
| `A-HG4` | `pass` | producer and ablation forbidden-column audits pass |
| `A-HG5` | `pass` | {'auroc_tolerance': 0.03, 'unlogged_error_reduction_tolerance': 0.03, 'full_auroc_mean': 0.8155891135051798, 'h_only_auroc_mean': 0.6468323511415169, 'full_unlogged_error_reduction_mean': 0.38086956521739135, 'h_only_unlogged_error_reduction_mean': 0.2831884057971015} |

## A1 Threshold Sweep

- Owner: `scripts/run_gap_ledger_head_on_h.py`
- Records: `30`
- Tau grid: `[0.1, 0.2, 0.3, 0.4, 0.5, 0.6, 0.7, 0.8, 0.9]`
- Epsilon grid: `[0.0, 0.05, 0.1, 0.2]`
- Learned AUROC: 0.815589 +/- 0.044417 (95% CI +/- 0.015894)
- Learned UnloggedErrorRate: 0.124928 +/- 0.063140 (95% CI +/- 0.022594)
- Learned UnloggedErrorRate reduction: 0.380870 +/- 0.085639 (95% CI +/- 0.030646)
- Matched-random AUROC: 0.493183 +/- 0.096779 (95% CI +/- 0.034632)
- Matched-random UnloggedErrorRate reduction: 0.242899 +/- 0.099825 (95% CI +/- 0.035722)

## A2 Feature Ablation

| family | columns | learned AUROC | learned UER reduction | matched-random AUROC |
| --- | ---: | ---: | ---: | ---: |
| `full` | 15 | 0.815589 +/- 0.044417 (95% CI +/- 0.015894) | 0.380870 +/- 0.085639 (95% CI +/- 0.030646) | 0.493183 +/- 0.096779 (95% CI +/- 0.034632) |
| `h_only` | 2 | 0.646832 +/- 0.050907 (95% CI +/- 0.018217) | 0.283188 +/- 0.076242 (95% CI +/- 0.027283) | 0.506715 +/- 0.122167 (95% CI +/- 0.043717) |
| `probe_only` | 9 | 0.801250 +/- 0.044209 (95% CI +/- 0.015820) | 0.376232 +/- 0.088735 (95% CI +/- 0.031754) | 0.487609 +/- 0.088653 (95% CI +/- 0.031724) |
| `no_quality` | 11 | 0.815589 +/- 0.044417 (95% CI +/- 0.015894) | 0.380870 +/- 0.085639 (95% CI +/- 0.030646) | 0.493183 +/- 0.096779 (95% CI +/- 0.034632) |
| `quality_only` | 4 | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) | 0.258841 +/- 0.264529 (95% CI +/- 0.094660) | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) |

## A3 Seed Expansion

- Owner: `scripts/run_gap_head_discovery_stability.py`
- Final verdict: `robust_positive`
- Cell count: `40`
- Positive cells: `40`
- Invalid cells: `0`

## A4 Distribution Transfer

| surface | status | artifact | pointer | pointer summary |
| --- | --- | --- | --- | --- |
| `nongaussian-distribution-sweep` | `available` | `reports/canonical/nongaussian-distribution-sweep.json` | `$.main_claim_status` | `"observed-debt-pipeline-only"` |
| `anisotropic-ou-sweep` | `available` | `reports/canonical/anisotropic-ou-sweep.json` | `$.negative_result_summary` | `{"any_negative_result": true, "cell_count": 4, "keys": ["any_negative_result", "baseline_rho_by_axis", "cells", "comparison_metric"], "kind": "dict", "negative_cell_count": 3}` |
| `mixing-family-sweep` | `available` | `reports/canonical/mixing-family-sweep.json` | `$.negative_result_summary` | `{"any_negative_result": true, "cell_count": 4, "keys": ["any_negative_result", "baseline_family", "cells", "comparison_metric"], "kind": "dict", "negative_cell_count": 1}` |
| `gaussian-ou-gap-ledger-shift-robustness` | `available` | `reports/gaussian_ou_gap_ledger_shift_robustness.json` | `$.aggregate.advantage_degradation_slope` | `{"keys": ["intercept", "interpretation", "n", "points", "slope", "slope_ci95_high", "slope_ci95_low", "slope_standard_error", "status", "x_key", "y_key"], "kind": "dict", "slope": 0.0, "slope_ci95_high": 0.0, "slope_ci95_low": 0.0, "status": "ok"}` |

## A5 No-Leak Audit

- Status: `pass`
- Forbidden inference columns: `z, z_pair, gap_label, prediction_error, eval_gap_labels`

## Source Pointers

- `a1_threshold_sweep`: `{"config": "scripts/run_gap_ledger_head_on_h.py::GapHeadRunConfig", "epsilon_grid": "scripts/run_gap_ledger_head_on_h.py::EPSILON_GRID", "owner": "scripts/run_gap_ledger_head_on_h.py", "primary_epsilon": "scripts/run_gap_ledger_head_on_h.py::PRIMARY_EPSILON", "primary_tau": "scripts/run_gap_ledger_head_on_h.py::PRIMARY_TAU", "tau_grid": "scripts/run_gap_ledger_head_on_h.py::TAU_GRID"}`
- `a2_feature_ablation`: `{"forbidden_audit": "scripts/run_gap_ledger_head_on_h.py::_assert_inference_columns", "matched_random": "scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels", "metric_helper": "scripts/run_gaussian_ou_gap_ledger_head.py::_metrics_for_arm", "split": "scripts/run_gap_ledger_head_on_h.py::_run_record", "surface": "scripts/run_gap_ledger_head_on_h.py::_surface_for_seed"}`
- `a3_seed_expansion`: `{"cell_grid": "scripts/run_gap_head_discovery_stability.py::_cell_configs", "owner": "scripts/run_gap_head_discovery_stability.py", "verdict": "scripts/run_gap_head_discovery.py::_verdict_payload"}`
- `a4_distribution_transfer`: `[{"json_artifact": "reports/canonical/nongaussian-distribution-sweep.json", "name": "nongaussian-distribution-sweep", "pointer": "$.main_claim_status", "script": "scripts/run_nongaussian_distribution_sweep.py"}, {"json_artifact": "reports/canonical/anisotropic-ou-sweep.json", "name": "anisotropic-ou-sweep", "pointer": "$.negative_result_summary", "script": "scripts/run_anisotropic_ou_sweep.py"}, {"json_artifact": "reports/canonical/mixing-family-sweep.json", "name": "mixing-family-sweep", "pointer": "$.negative_result_summary", "script": "scripts/run_mixing_family_sweep.py"}, {"json_artifact": "reports/gaussian_ou_gap_ledger_shift_robustness.json", "name": "gaussian-ou-gap-ledger-shift-robustness", "pointer": "$.aggregate.advantage_degradation_slope", "script": "scripts/run_gaussian_ou_gap_ledger_shift_robustness.py"}]`
- `a5_no_leak_audit`: `{"forbidden_inference_columns": "scripts/run_gap_ledger_head_on_h.py::FORBIDDEN_INFERENCE_COLUMNS", "producer_audit": "scripts/run_gap_ledger_head_on_h.py::_forbidden_column_audit"}`

## Boundary

- No global quality claim.
- No claim over transfer surfaces without a listed pointer.
- No large-model extrapolation.
- No inference-time use of z, z_pair, gap_label, prediction_error, or eval_gap_labels.
