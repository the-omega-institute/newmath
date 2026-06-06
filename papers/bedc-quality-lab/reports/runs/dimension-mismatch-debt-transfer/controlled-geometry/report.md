# Dimension-Mismatch Debt Transfer Claim Capsule

- Source artifact: `reports/canonical/dimension-mismatch-debt-transfer.json`
- Source pointer: `$.dimension_mismatch_debt_transfer`
- Controlled geometry artifact: `reports/dimension_mismatch_anti_triviality.json`
- Controlled geometry pointer: `$.controlled_geometry`
- Claim capsule pointer: `reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json:$.run_local`
- Status: `pass`
- Effective level: `DN`

## Negative Witness Pointers

| witness | owner pointer | source pointer | regression pointer |
| --- | --- | --- | --- |
| `scale_leakage_witness` | `$.run_local.negative_witness[0]` | `reports/dimension_mismatch_anti_triviality.json:$.status` | `$.run_local.test_artifact.regression_tests.scale_leakage_witness` |
