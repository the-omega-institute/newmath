# Dimension-Mismatch Transfer Robustness

- Status: `pass`
- Artifact id: `bedc-quality-lab:dimension-mismatch-transfer-robustness`
- Source pointer: `reports/canonical/dimension-mismatch-debt-transfer.json:$.dimension_mismatch_debt_transfer.status`
- Readiness boundary: pass = robust-control evidence for the source dimension-mismatch-debt-transfer surface with terminal DN downgrade under anti-triviality; not a D5 upgrade, not global model quality.

## Robust control checks

| check | verdict | evidence pointer | reason |
| --- | --- | --- | --- |
| `HG-DM-R1` | `pass` | `reports/canonical/dimension-mismatch-debt-transfer.json:$.hardgate_evidence.HG-B3` | source status, non-stub boundary, and learned-over-matched-random evidence resolve |
| `HG-DM-R2` | `pass` | `reports/canonical/dimension-mismatch-debt-transfer.json:$.hardgate_evidence.HG-B3.learned_minus_matched_random_auroc.ci95_low` | learned-minus-matched-random AUROC lower confidence bound is positive |
| `HG-DM-R3` | `pass` | `reports/canonical/dimension-mismatch-debt-transfer.json:$.control_protocol` | matched-random and vanilla controls resolve under the same h-only protocol |
| `HG-DM-R4` | `pass` | `reports/canonical/dimension-mismatch-debt-transfer.json:$.hardgate_evidence.HG-B4.audit.actual_model_input_columns` | actual model input columns exactly match the declared h-only allowlist |
| `HG-DM-R5` | `pass` | `reports/canonical/dimension-mismatch-debt-transfer.json:$.hardgate_evidence.HG-B5.audit.hits` | claim boundary has no forbidden positive terms and no aggregate ordering surface |
| `HG-DM-R6` | `pass` | `reports/dimension_mismatch_anti_triviality.json:$.controlled_geometry.control_family_coverage.family_pointers` | all six control-family pointers resolve and folded-source coverage is consistent |

## Audit

- Audit status: `pass`
- Audit pointer: `reports/canonical/negative_discovery_reports.json:$.rows[4]`
- Failed or deferred gates: ``
