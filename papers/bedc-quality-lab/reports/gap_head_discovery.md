# Gap-Head Discovery Verdict

- Source JSON artifact: `reports/gap_ledger_head_on_h.json`
- Source report artifact: `reports/gap_ledger_head_on_h.md`
- Common-source record count: `30`
- Surface delta count: `30`
- Shift information: `30`
- Structural discovery: `true`
- Positive discovery: `true`
- Non-discovery reason: `none`

## Information

- Benefit: `0.917681`
- Score: `0.190000`
- Debt: `0.350000`
- Omitted debt: `0.000000`
- Net: `0.377681`

## Boundary

- Representation boundary: `learned_h`
- Inference no ground-truth z: `true`
- Before arm: `vanilla`
- After arm: `learned_gap_head_on_h`
- Forbidden inference columns: `z, z_pair, gap_label, prediction_error, eval_gap_labels`

## Cost Protocol

- Benefit terms:
  - `unlogged_error_reduction`: `0.400870`
  - `critical_unlogged_error_reduction`: `0.516812`
- Score terms:
  - `h_only_feature_surface`: `0.150000`
  - `gap_channel_heads`: `0.040000`
- Debt terms:
  - `classifier_ledger_rows`: `0.300000`
  - `boundary_protocol`: `0.050000`

## Source Artifacts

- `source_json_artifact`: `reports/gap_ledger_head_on_h.json`
- `source_report_artifact`: `reports/gap_ledger_head_on_h.md`
- `producer_script`: `scripts/run_gap_ledger_head_on_h.py`
- `projection_script`: `scripts/run_gap_head_discovery.py`
