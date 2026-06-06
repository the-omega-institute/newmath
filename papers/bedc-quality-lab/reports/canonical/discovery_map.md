# Discovery Map

- Generated at: `2026-06-05T07:13:11.713087+00:00`
- Rows: `24`

| report | level | base | mechanism | projection | audit | evidence |
| --- | --- | --- | --- | --- | --- | --- |
| `mixing-family-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.coverage_item.debt_item` |
| `anisotropic-ou-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.transition_debt_by_grid` |
| `gap-head-on-h` | `D5-O` | `` | `` | `projected` | `valid` | `$.control_protocol` |
| `gap-head-discovery` | `D4` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `gap-head-ablation` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[0]` |
| `ledger-aware-transformer` | `D4` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `certificate-gated-attention` | `D4` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `gap-head-threshold-frontier` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `gap-head-transfer-atlas` | `D5-O` | `` | `` | `projected` | `valid` | `$.config.control_arm` |
| `gap-head-attribution-capsule` | `D0` | `D5-O` | `blocked` | `two-axis-recorded` | `valid` | `$.mechanism_evidence` |
| `nongaussian-distribution-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.negative_result_ledger` |
| `certificate-guided-training` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[1]` |
| `certificate-guided-discovery` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[2]` |
| `sigreg-training-proxy` | `D1` | `` | `` | `projected` | `valid` | `$.d1_evidence.debt_delta` |
| `sigreg-mini-grid` | `D2` | `` | `` | `projected` | `valid` | `$.trend_summary.expected_trend` |
| `discovery-regularized-training` | `D4` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `mechanism-seeking-network` | `D4` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `discovery-gated-nas` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[3]` |
| `lejepa-theorem-ledger` | `D0` | `` | `` | `theorem-ledger-recorded` | `valid` | `$.theorem_rows` |
| `spectral-ablation-hinge` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[4]` |
| `dimension-mismatch-debt-transfer` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[5]` |
| `single-threshold-escape` | `DN` | `` | `` | `escaped-positive-captured` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[6]` |
| `training-choice-observability` | `DN` | `` | `` | `pointer-only` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[7]` |
| `gap-head-mechanism-blockage` | `DN` | `` | `` | `mechanism-blockage-projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[8]` |

## D5 readiness

### gap-head-on-h

- `threshold`: `pass` (reports/canonical/gap-head-robustness-sweep.json:$.A1_threshold_sweep.treatment_verdict.positive) A1 threshold sweep passes under the canonical robustness final_status.
- `ablation`: `pass` (reports/canonical/gap-head-robustness-sweep.json:$.A2_feature_ablation.status) A2 feature ablation is complete under the canonical robustness final_status.
- `seed_expansion`: `pass` (reports/canonical/gap-head-robustness-sweep.json:$.A3_seed_expansion.final_verdict) A3 seed expansion has robust_positive final verdict under final_status=pass.
- `adversarial`: `pass` (reports/canonical/discovery_negative_witnesses.json:$.witnesses) The eight adversarial witness kinds do not break the discovery gate.
- `observed_debt_transfer`: `pass` (reports/canonical/gap-head-observed-debt-transfer.json:$.gap_head_on_h_observed_debt_transfer.status) Observed-debt transfer metric for gap-head-on-h passes.

## Coverage matrix

- Status: `pointer-only`
- Overall state: `present`

| target | owner pointer | slot state |
| --- | --- | --- |
| `anisotropic-ou-sweep` | `reports/canonical/anisotropic-ou-sweep.json:$.transition_debt_by_grid` | `present` |
| `certificate-gated-attention` | `reports/canonical/certificate-gated-attention.json:$.certificate_gate_summary.gated_vs_plain_valid` | `present` |
| `certificate-guided-discovery` | `reports/canonical/negative_discovery_reports.json:$.rows[2]` | `negative` |
| `certificate-guided-training` | `reports/canonical/negative_discovery_reports.json:$.rows[1]` | `negative` |
| `dimension-mismatch-debt-transfer` | `reports/canonical/negative_discovery_reports.json:$.rows[5]` | `negative` |
| `discovery-gated-nas` | `reports/canonical/negative_discovery_reports.json:$.rows[3]` | `negative` |
| `discovery-regularized-training` | `reports/canonical/discovery-regularized-training.json:$.torch_training_evidence` | `present` |
| `gap-head-ablation` | `reports/canonical/negative_discovery_reports.json:$.rows[0]` | `negative` |
| `gap-head-attribution-capsule` | `reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence` | `present` |
| `gap-head-discovery` | `reports/canonical/gap-head-discovery.json:$.positive_discovery` | `present` |
| `gap-head-mechanism-blockage` | `reports/canonical/negative_discovery_reports.json:$.rows[8]` | `negative` |
| `gap-head-on-h` | `reports/canonical/gap-head-on-h.json:$.treatment_verdict.positive` | `present` |
| `gap-head-threshold-frontier` | `reports/canonical/discovery_map.json:$.rows[7]` | `present` |
| `gap-head-transfer-atlas` | `reports/canonical/gap_head_transfer_atlas.json:$.multi_surface_d5_o.decision` | `present` |
| `ledger-aware-transformer` | `reports/canonical/ledger-aware-transformer.json:$.aggregate_metrics.uer_reduction` | `present` |
| `lejepa-theorem-ledger` | `reports/canonical/lejepa_theorem_ledger.json:$.theorem_rows` | `present` |
| `mechanism-seeking-network` | `reports/canonical/mechanism-seeking-network.json:$.mechanism_gate_summary` | `present` |
| `mixing-family-sweep` | `reports/canonical/mixing-family-sweep.json:$.coverage_item.debt_item` | `present` |
| `nongaussian-distribution-sweep` | `reports/canonical/nongaussian-distribution-sweep.json:$.negative_result_ledger` | `present` |
| `sigreg-mini-grid` | `reports/canonical/sigreg-mini-grid.json:$.trend_summary.expected_trend` | `present` |
| `sigreg-training-proxy` | `reports/canonical/sigreg-training-proxy.json:$.d1_evidence.debt_delta` | `present` |
| `single-threshold-escape` | `reports/canonical/negative_discovery_reports.json:$.rows[6]` | `negative` |
| `spectral-ablation-hinge` | `reports/canonical/negative_discovery_reports.json:$.rows[4]` | `negative` |
| `training-choice-observability` | `reports/canonical/negative_discovery_reports.json:$.rows[7]` | `negative` |
