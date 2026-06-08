# Negative Discovery Reports

- Generated at: `2026-06-08T09:11:15.361169+00:00`
- Status: `pointer-only`
- Rows: `8`

| negative id | report id | claim | failed gate | source | audit |
| --- | --- | --- | --- | --- | --- |
| `dn:gap-head-ablation` | `gap-head-ablation` | `claim:gap-head-ablation` | `$.hardgate.status` | `reports/canonical/gap-head-ablation.json:$.hardgate.status` | `pass` |
| `dn:certificate-guided-training` | `certificate-guided-training` | `claim:certificate-guided-training` | `$.claim_capsule.terminal_verdict` | `reports/canonical/certificate-guided-training.json:$.claim_capsule.terminal_verdict` | `pass` |
| `dn:certificate-guided-discovery` | `certificate-guided-discovery` | `claim:certificate-guided-discovery` | `$.positive_discovery` | `reports/canonical/certificate-guided-discovery.json:$.positive_discovery` | `pass` |
| `dn:discovery-gated-nas` | `discovery-gated-nas` | `claim:discovery-gated-nas` | `$.hardgate.gates.DG-NAS-HG8.status` | `reports/canonical/discovery-gated-nas.json:$.hardgate.gates.DG-NAS-HG8.status` | `pass` |
| `dn:spectral-ablation-hinge` | `spectral-ablation-hinge` | `claim:spectral-ablation-hinge` | `$.negative_control_summary.treatment_better_than_all_controls` | `reports/canonical/spectral-ablation-hinge.json:$.negative_control_summary.treatment_better_than_all_controls` | `pass` |
| `dn:dimension-mismatch-scale-leakage` | `dimension-mismatch-scale-leakage` | `claim:dimension-mismatch-debt-transfer` | `$.dimension_mismatch_debt_transfer.anti_triviality_status` | `reports/canonical/dimension-mismatch-debt-transfer.json:$.dimension_mismatch_debt_transfer.anti_triviality_status` | `pass` |
| `dn:single-threshold-escape` | `single-threshold-escape` | `claim:single-threshold-escape` | `$.projection.escaped_positive_is_discovery_evidence` | `runs/single_threshold_escape_witness.json:$.projection.escaped_positive_is_discovery_evidence` | `pass` |
| `dn:training-choice-observability` | `training-choice-observability` | `claim:training-choice-observability` | `$.training_choice_observability.ledger_risk_only_arm_count` | `runs/training_choice_observability.json:$.training_choice_observability.ledger_risk_only_arm_count` | `pass` |
