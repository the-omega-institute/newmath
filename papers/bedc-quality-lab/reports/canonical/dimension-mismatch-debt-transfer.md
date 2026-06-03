# Dimension-Mismatch Debt Transfer

- JSON artifact pointer: `reports/canonical/dimension-mismatch-debt-transfer.json`
- Report artifact pointer: `reports/canonical/dimension-mismatch-debt-transfer.md`
- Artifact id pointer: `$.artifact_id`
- Transfer status pointer: `$.dimension_mismatch_debt_transfer.status`
- Boundary ledger pointer: `$.boundary_ledger`
- H-only allowlist pointer: `$.representation_boundary.declared_h_only_allowlist`
- Source pointers: `$.source_artifacts`

## Metric rows

| metric | arm | mean | ci95 low | ci95 high | source pointer |
| --- | --- | ---: | ---: | ---: | --- |
| `failure_detection_auroc` | `vanilla` | 0.500000 | 0.500000 | 0.500000 | `$.metrics.by_arm` |
| `failure_detection_auroc` | `learned_h_summary_head` | 1.000000 | 1.000000 | 1.000000 | `$.metrics.by_arm` |
| `failure_detection_auroc` | `matched_random_gap_head` | 0.620870 | 0.411466 | 0.830274 | `$.metrics.by_arm` |
| `failure_detection_auroc_delta` | `learned_minus_matched_random` | 0.379130 | 0.169726 | 0.588534 | `$.metrics.comparison` |

## Boundary

| field | value | pointer |
| --- | --- | --- |
| status | `pass` | `$.dimension_mismatch_debt_transfer.status` |
| status code | `scoped-d4-boundary` | `$.dimension_mismatch_debt_transfer.status_code` |
| discovery level | `D4` | `$.dimension_mismatch_debt_transfer.discovery_level` |
| scope | `encoder_dim grid against producer reference latent dimension` | `$.dimension_mismatch_debt_transfer.scope` |
