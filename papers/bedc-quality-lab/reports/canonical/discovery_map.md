# Discovery Map

- Generated at: `2026-06-03T15:47:35.771561+00:00`
- Rows: `10`

| report | level | projection | audit | evidence |
| --- | --- | --- | --- | --- |
| `mixing-family-sweep` | `D1` | `projected` | `valid` | `$.coverage_item.debt_item` |
| `anisotropic-ou-sweep` | `D1` | `projected` | `valid` | `$.transition_debt_by_grid` |
| `gap-head-on-h` | `D5` | `projected` | `valid` | `$.control_protocol` |
| `gap-head-discovery` | `D4` | `projected` | `valid` | `$.matched_random_control` |
| `gap-head-ablation` | `DN` | `projected` | `valid` | `$.hardgate.status` |
| `gap-head-threshold-frontier` | `D0` | `source-insufficient` | `valid` | `source-insufficient` |
| `nongaussian-distribution-sweep` | `D1` | `projected` | `valid` | `$.negative_result_ledger` |
| `certificate-guided-training` | `DN` | `projected` | `valid` | `$.result.status` |
| `certificate-guided-discovery` | `DN` | `projected` | `valid` | `$.positive_discovery` |
| `spectral-ablation-hinge` | `DN` | `projected` | `valid` | `$.negative_control_summary.treatment_better_than_all_controls` |

## D5 readiness

### gap-head-on-h

- `threshold`: `pass` (reports/canonical/gap-head-robustness-sweep.json:$.A1_threshold_sweep.treatment_verdict.positive) A1 threshold sweep passes under the canonical robustness final_status.
- `ablation`: `pass` (reports/canonical/gap-head-robustness-sweep.json:$.A2_feature_ablation.status) A2 feature ablation is complete under the canonical robustness final_status.
- `seed_expansion`: `pass` (reports/canonical/gap-head-robustness-sweep.json:$.A3_seed_expansion.final_verdict) A3 seed expansion has robust_positive final verdict under final_status=pass.
- `adversarial`: `pass` (reports/canonical/discovery_negative_witnesses.json:$.witnesses) The eight adversarial witness kinds do not break the discovery gate.
- `observed_debt_transfer`: `pass` (reports/canonical/gap-head-observed-debt-transfer.json:$.gap_head_on_h_observed_debt_transfer.status) Observed-debt transfer metric for gap-head-on-h passes.
