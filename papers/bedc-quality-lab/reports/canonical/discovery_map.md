# Discovery Map

- Generated at: `2026-06-05T07:13:11.713087+00:00`
- Rows: `17`

| report | level | base | mechanism | projection | audit | evidence |
| --- | --- | --- | --- | --- | --- | --- |
| `mixing-family-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.coverage_item.debt_item` |
| `anisotropic-ou-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.transition_debt_by_grid` |
| `gap-head-on-h` | `D5-O` | `` | `` | `projected` | `valid` | `$.control_protocol` |
| `gap-head-discovery` | `D4` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `gap-head-ablation` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[0]` |
| `gap-head-threshold-frontier` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `gap-head-transfer-atlas` | `D5-O` | `` | `` | `projected` | `valid` | `$.config.control_arm` |
| `gap-head-attribution-capsule` | `D0` | `D5-O` | `blocked` | `two-axis-recorded` | `valid` | `$.mechanism_evidence` |
| `nongaussian-distribution-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.negative_result_ledger` |
| `certificate-guided-training` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[1]` |
| `certificate-guided-discovery` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[2]` |
| `sigreg-training-proxy` | `D1` | `` | `` | `projected` | `valid` | `$.d1_evidence.debt_delta` |
| `lejepa-theorem-ledger` | `D0` | `` | `` | `theorem-ledger-recorded` | `valid` | `$.theorem_rows` |
| `spectral-ablation-hinge` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[3]` |
| `dimension-mismatch-debt-transfer` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[4]` |
| `single-threshold-escape` | `DN` | `` | `` | `escaped-positive-captured` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[5]` |
| `training-choice-observability` | `DN` | `` | `` | `pointer-only` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[6]` |

## D5 readiness

### gap-head-on-h

- `threshold`: `pass` (reports/canonical/gap-head-robustness-sweep.json:$.A1_threshold_sweep.treatment_verdict.positive) A1 threshold sweep passes under the canonical robustness final_status.
- `ablation`: `pass` (reports/canonical/gap-head-robustness-sweep.json:$.A2_feature_ablation.status) A2 feature ablation is complete under the canonical robustness final_status.
- `seed_expansion`: `pass` (reports/canonical/gap-head-robustness-sweep.json:$.A3_seed_expansion.final_verdict) A3 seed expansion has robust_positive final verdict under final_status=pass.
- `adversarial`: `pass` (reports/canonical/discovery_negative_witnesses.json:$.witnesses) The eight adversarial witness kinds do not break the discovery gate.
- `observed_debt_transfer`: `pass` (reports/canonical/gap-head-observed-debt-transfer.json:$.gap_head_on_h_observed_debt_transfer.status) Observed-debt transfer metric for gap-head-on-h passes.
