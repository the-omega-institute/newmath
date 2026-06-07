# Gap-Head Discovery Verdict

- Source JSON artifact: `reports/canonical/gap-head-on-h.json`
- Source report artifact: `reports/canonical/gap-head-on-h.md`
- Common-source record count: `30`
- Surface delta count: `30`
- Shift information: `30`
- Structural discovery: `true`
- Positive discovery: `true`
- Main claim status: `promoted`
- Non-discovery reason: `none`
- Matched-random control positive: `false`

## Information

- Benefit: `0.886087`
- Score: `0.190000`
- Debt: `0.350000`
- Omitted debt: `0.000000`
- Net: `0.346087`

## Boundary

- Representation boundary: `learned_h`
- Inference no ground-truth z: `true`
- Before arm: `vanilla`
- After arm: `learned_gap_head_on_h`
- Forbidden inference columns: `label, z, z_pair, gap_label, gap_labels, prediction_error, eval_label, eval_labels, eval_gap_label, eval_gap_labels, config_metadata`

## Cost Protocol

- Benefit terms:
  - `unlogged_error_reduction`: `0.380870`
  - `critical_unlogged_error_reduction`: `0.505217`
- Score terms:
  - `h_only_feature_surface`: `0.150000`
  - `gap_channel_heads`: `0.040000`
- Debt terms:
  - `classifier_ledger_rows`: `0.300000`
  - `boundary_protocol`: `0.050000`

## Source Artifacts

- `source_json_artifact`: `reports/canonical/gap-head-on-h.json`
- `source_report_artifact`: `reports/canonical/gap-head-on-h.md`
- `producer_script`: `scripts/run_gap_ledger_head_on_h.py`
- `projection_script`: `scripts/run_gap_head_discovery.py`
