# Discovery Map

- Generated at: `2026-06-07T00:00:00+00:00`
- Rows: `24`

| report | level | base | mechanism | projection | audit | evidence |
| --- | --- | --- | --- | --- | --- | --- |
| `mixing-family-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.coverage_item.debt_item` |
| `anisotropic-ou-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.transition_debt_by_grid` |
| `gap-head-on-h` | `D5-O` | `` | `` | `projected` | `valid` | `$.control_protocol` |
| `gap-head-discovery` | `D4` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `gap-head-ablation` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[0]` |
| `ledger-aware-transformer` | `D5-O` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `certificate-gated-attention` | `D4` | `` | `` | `projected` | `valid` | `$.route_patch_protocol` |
| `gap-head-threshold-frontier` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `gap-head-transfer-atlas` | `D5-O` | `` | `` | `projected` | `valid` | `$.config.control_arm` |
| `gap-head-attribution-capsule` | `D0` | `D5-O` | `blocked` | `two-axis-recorded` | `valid` | `$.mechanism_evidence` |
| `nongaussian-distribution-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.negative_result_ledger` |
| `certificate-guided-training` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[1]` |
| `certificate-guided-discovery` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[2]` |
| `sigreg-training-proxy` | `D1` | `` | `` | `projected` | `valid` | `$.d1_evidence.debt_delta` |
| `sigreg-mini-grid` | `D2` | `` | `` | `projected` | `valid` | `$.trend_summary.expected_trend` |
| `discovery-regularized-training` | `D5-M` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
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

| hardgate | status | reason |
| --- | --- | --- |
| `COV-HG1-owner` | `pass` | every cell has a resolvable canonical owner pointer |
| `COV-HG2-resolves` | `pass` | every non-null coverage pointer resolves |
| `COV-HG3-pointer-only` | `pass` | coverage matrix contains only pointer fields and gate summaries |
| `COV-HG4-positive-support` | `pass` | positive and model-design cells point to mechanism support or debt |
| `COV-HG5-dn-witness` | `pass` | DN cells point to canonical negative witnesses |
| `COV-HG6-complete-set` | `pass` | coverage cells match the required component set |

| group | component | owner pointer | hardgate |
| --- | --- | --- | --- |
| `positive` | `CGA` | `reports/canonical/certificate-gated-attention.json:$` | `pass` |
| `positive` | `DG-NAS` | `reports/canonical/discovery-gated-nas.json:$` | `pass` |
| `positive` | `DGT` | `reports/canonical/discovery_gated_transformer.json:$` | `pass` |
| `positive` | `DRT` | `reports/canonical/discovery-regularized-training.json:$` | `pass` |
| `positive` | `LAT` | `reports/canonical/ledger-aware-transformer.json:$` | `pass` |
| `negative` | `LeJEPA-mini-grid-DN` | `reports/runs/lejepa-mini-grid/claim_capsule.json:$` | `pass` |
| `positive` | `MSN` | `reports/canonical/mechanism-seeking-network.json:$` | `pass` |
| `negative` | `certificate-guided-DN` | `reports/canonical/negative_discovery_reports.json:$.rows[1]` | `pass` |
| `negative` | `dimension-mismatch-DN` | `reports/canonical/dimension-mismatch-debt-transfer.json:$` | `pass` |
| `positive` | `gap-head-mech` | `reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence` | `pass` |
| `positive` | `gap-head-op` | `reports/canonical/gap-head-robustness-sweep.json:$.acceptance_gates.status` | `pass` |
| `positive` | `lejepa-theorem-ledger` | `reports/canonical/lejepa_theorem_ledger.json:$` | `pass` |
| `positive` | `sigreg-mini-grid` | `reports/canonical/sigreg-mini-grid.json:$` | `pass` |

## Experiment proposals

| proposal id | source kind | source pointer | failed gate pointer | status |
| --- | --- | --- | --- | --- |
| `exp-d5m-gap-head-attribution-capsule` | `d5m_blocked` | `reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence` | `reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence.failed_gate` | `proposed` |
| `exp-dn-gap-head-ablation` | `negative_discovery` | `reports/canonical/negative_discovery_reports.json:$.rows[0]` | `reports/canonical/negative_discovery_reports.json:$.rows[0].failed_gate` | `proposed` |
| `exp-dn-certificate-guided-training` | `negative_discovery` | `reports/canonical/negative_discovery_reports.json:$.rows[1]` | `reports/canonical/negative_discovery_reports.json:$.rows[1].failed_gate` | `proposed` |
| `exp-dn-certificate-guided-discovery` | `negative_discovery` | `reports/canonical/negative_discovery_reports.json:$.rows[2]` | `reports/canonical/negative_discovery_reports.json:$.rows[2].failed_gate` | `proposed` |
| `exp-dn-discovery-gated-nas` | `negative_discovery` | `reports/canonical/negative_discovery_reports.json:$.rows[3]` | `reports/canonical/negative_discovery_reports.json:$.rows[3].failed_gate` | `proposed` |
| `exp-dn-spectral-ablation-hinge` | `negative_discovery` | `reports/canonical/negative_discovery_reports.json:$.rows[4]` | `reports/canonical/negative_discovery_reports.json:$.rows[4].failed_gate` | `proposed` |
| `exp-dn-dimension-mismatch-debt-transfer` | `negative_discovery` | `reports/canonical/negative_discovery_reports.json:$.rows[5]` | `reports/canonical/negative_discovery_reports.json:$.rows[5].failed_gate` | `proposed` |
| `exp-dn-single-threshold-escape` | `negative_discovery` | `reports/canonical/negative_discovery_reports.json:$.rows[6]` | `reports/canonical/negative_discovery_reports.json:$.rows[6].failed_gate` | `proposed` |
| `exp-dn-training-choice-observability` | `negative_discovery` | `reports/canonical/negative_discovery_reports.json:$.rows[7]` | `reports/canonical/negative_discovery_reports.json:$.rows[7].failed_gate` | `proposed` |
| `exp-dn-gap-head-mechanism-blockage` | `negative_discovery` | `reports/canonical/negative_discovery_reports.json:$.rows[8]` | `reports/canonical/negative_discovery_reports.json:$.rows[8].failed_gate` | `proposed` |
| `exp-coverage-cga` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[0]` | `` | `proposed` |
| `exp-coverage-dg-nas` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[1]` | `` | `proposed` |
| `exp-coverage-dgt` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[2]` | `` | `proposed` |
| `exp-coverage-drt` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[3]` | `` | `proposed` |
| `exp-coverage-lat` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[4]` | `` | `proposed` |
| `exp-coverage-lejepa-mini-grid-dn` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[5]` | `` | `proposed` |
| `exp-coverage-msn` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[6]` | `` | `proposed` |
| `exp-coverage-certificate-guided-dn` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[7]` | `` | `proposed` |
| `exp-coverage-dimension-mismatch-dn` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[8]` | `` | `proposed` |
| `exp-coverage-gap-head-mech` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[9]` | `` | `proposed` |
| `exp-coverage-gap-head-op` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[10]` | `` | `proposed` |
| `exp-coverage-lejepa-theorem-ledger` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[11]` | `` | `proposed` |
| `exp-coverage-sigreg-mini-grid` | `coverage_gap` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[12]` | `` | `proposed` |
