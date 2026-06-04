# Gap-Head Mechanism Attribution

- Generated at: `2026-06-04T11:04:50.081457+00:00`
- Artifact: `bedc-quality-lab:gap-head-mechanism-attribution`
- Sidecar role: `pointer_only_non_canonical`
- Mechanism status: `probe-margin-channel`
- Demotion channel: `score_plus_margin`
- Arm count: `16`

## Arms

| arm | learned AUROC | learned UER reduction | matched-random AUROC | alias | gating role |
| --- | ---: | ---: | ---: | --- | --- |
| `full` | 0.815589 +/- 0.044417 (95% CI +/- 0.015894) | 0.380870 +/- 0.085639 (95% CI +/- 0.030646) | 0.493183 +/- 0.096779 (95% CI +/- 0.034632) | `None` | `gating_candidate` |
| `h_only` | 0.646832 +/- 0.050907 (95% CI +/- 0.018217) | 0.283188 +/- 0.076242 (95% CI +/- 0.027283) | 0.506715 +/- 0.122167 (95% CI +/- 0.043717) | `None` | `gating_candidate` |
| `h_direction_only` | 0.556672 +/- 0.055516 (95% CI +/- 0.019866) | 0.273333 +/- 0.120224 (95% CI +/- 0.043021) | 0.482611 +/- 0.067533 (95% CI +/- 0.024166) | `None` | `gating_candidate` |
| `h_norm_only` | 0.522143 +/- 0.055188 (95% CI +/- 0.019749) | 0.247246 +/- 0.184104 (95% CI +/- 0.065881) | 0.513552 +/- 0.057990 (95% CI +/- 0.020752) | `None` | `gating_candidate` |
| `h_normalized_no_scale` | 0.556672 +/- 0.055516 (95% CI +/- 0.019866) | 0.273333 +/- 0.120224 (95% CI +/- 0.043021) | 0.482611 +/- 0.067533 (95% CI +/- 0.024166) | `h_direction_only` | `non_gating_alias` |
| `score_only` | 0.796595 +/- 0.051474 (95% CI +/- 0.018420) | 0.368116 +/- 0.086304 (95% CI +/- 0.030884) | 0.487624 +/- 0.182803 (95% CI +/- 0.065415) | `None` | `gating_candidate` |
| `margin_only` | 0.568055 +/- 0.058254 (95% CI +/- 0.020846) | 0.266087 +/- 0.138560 (95% CI +/- 0.049583) | 0.529810 +/- 0.062816 (95% CI +/- 0.022478) | `None` | `gating_candidate` |
| `transition_delta_only` | 0.536348 +/- 0.066504 (95% CI +/- 0.023798) | 0.246957 +/- 0.142822 (95% CI +/- 0.051108) | 0.503935 +/- 0.054980 (95% CI +/- 0.019674) | `None` | `gating_candidate` |
| `quality_scalars_only` | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) | 0.258841 +/- 0.264529 (95% CI +/- 0.094660) | 0.500000 +/- 0.000000 (95% CI +/- 0.000000) | `None` | `gating_candidate` |
| `score_plus_margin` | 0.813746 +/- 0.052432 (95% CI +/- 0.018762) | 0.381449 +/- 0.094230 (95% CI +/- 0.033720) | 0.494166 +/- 0.105661 (95% CI +/- 0.037810) | `None` | `gating_candidate` |
| `h_plus_margin` | 0.665109 +/- 0.052792 (95% CI +/- 0.018891) | 0.336812 +/- 0.100190 (95% CI +/- 0.035853) | 0.519316 +/- 0.080126 (95% CI +/- 0.028673) | `None` | `gating_candidate` |
| `h_plus_transition` | 0.649792 +/- 0.057584 (95% CI +/- 0.020606) | 0.306667 +/- 0.086684 (95% CI +/- 0.031020) | 0.500031 +/- 0.094507 (95% CI +/- 0.033819) | `None` | `gating_candidate` |
| `full_without_margin` | 0.805031 +/- 0.046021 (95% CI +/- 0.016469) | 0.368116 +/- 0.083572 (95% CI +/- 0.029906) | 0.487929 +/- 0.116390 (95% CI +/- 0.041650) | `None` | `gating_candidate` |
| `full_without_transition` | 0.826162 +/- 0.049520 (95% CI +/- 0.017720) | 0.388406 +/- 0.087056 (95% CI +/- 0.031153) | 0.499633 +/- 0.112199 (95% CI +/- 0.040150) | `None` | `gating_candidate` |
| `full_without_quality_scalars` | 0.815589 +/- 0.044417 (95% CI +/- 0.015894) | 0.380870 +/- 0.085639 (95% CI +/- 0.030646) | 0.493183 +/- 0.096779 (95% CI +/- 0.034632) | `None` | `gating_candidate` |
| `matched_random` | 0.493183 +/- 0.096779 (95% CI +/- 0.034632) | 0.242899 +/- 0.099825 (95% CI +/- 0.035722) | 0.493183 +/- 0.096779 (95% CI +/- 0.034632) | `None` | `gating_candidate` |

## HG-A1 Gates

| gate | status |
| --- | --- |
| `HG-A1-1` | `pass` |
| `HG-A1-2` | `pass` |
| `HG-A1-3` | `fail` |
| `HG-A1-4` | `fail` |
| `HG-A1-5` | `probe-margin-channel` |

## Alias Metadata

- `h_normalized_no_scale` is a non-gating alias of `h_direction_only`; it reuses the row-L2 unit-direction matrix, does not train-center, and is excluded as an independent demotion channel.

## Source Pointers

- artifact_id: `bedc-quality-lab:gap-head-mechanism-attribution`
- generation_script: `scripts/run_gap_head_mechanism_attribution.py`
- source_surface: `scripts/run_gap_ledger_head_on_h.py::_surface_for_seed`
- source_fit_helper: `scripts/run_gap_ledger_head_on_h.py::_fit_gap_head`
- source_predict_helper: `scripts/run_gap_ledger_head_on_h.py::_predict_gap_head`
- source_metric_helper: `scripts/run_gap_ledger_head_on_h.py::_metrics_for_arm`
- source_matched_random_helper: `scripts/run_gap_ledger_head_on_h.py::_matched_random_gap_labels`
- source_forbidden_column_audit: `scripts/run_gap_ledger_head_on_h.py::_assert_inference_columns`
- source_config: `scripts/run_gap_ledger_head_on_h.py::GapHeadRunConfig`
- json_artifact: `reports/gap_head_mechanism_attribution.json`
- report_artifact: `reports/gap_head_mechanism_attribution.md`
- canonical_status: `sidecar_not_canonical`

## Not Claimed

- No global quality claim.
- No full LeJEPA claim.
- No full Tensor NameCert claim.
- No LLM behavior claim.
- No canonical discovery-map promotion from this sidecar.
