# Discovery Map

- Generated at: `2026-06-12T15:27:47.465919+00:00`
- Rows: `40`

| report | level | base | mechanism | projection | audit | evidence |
| --- | --- | --- | --- | --- | --- | --- |
| `mixing-family-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.coverage_item.debt_item` |
| `anisotropic-ou-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.transition_debt_by_grid` |
| `gap-head-on-h` | `D4` | `` | `` | `projected` | `valid` | `$.control_protocol` |
| `gap-head-discovery` | `D4` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `gap-head-ablation` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[0]` |
| `irreducibility-report` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `ledger-aware-transformer` | `D5-O` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `certificate-gated-attention` | `D4` | `` | `` | `projected` | `valid` | `$.route_patch_protocol` |
| `gap-head-threshold-frontier` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `gap-head-transfer-atlas` | `D5-O` | `` | `` | `projected` | `valid` | `$.config.control_arm` |
| `gap-head-attribution-capsule` | `D0` | `` | `` | `two-axis-recorded` | `invalid` | `$.mechanism_evidence` |
| `nongaussian-distribution-sweep` | `D1` | `` | `` | `projected` | `valid` | `$.negative_result_ledger` |
| `certificate-guided-training` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[1]` |
| `certificate-guided-discovery` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[2]` |
| `sigreg-training-proxy` | `D1` | `` | `` | `projected` | `valid` | `$.d1_evidence.debt_delta` |
| `sigreg-mini-grid` | `D2` | `` | `` | `projected` | `valid` | `$.trend_summary.expected_trend` |
| `discovery-regularized-training` | `D5-M` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `mechanism-seeking-network` | `D4` | `` | `` | `projected` | `valid` | `$.matched_random_control` |
| `mechanism-dna` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `dgt-l0-controls` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `winnability-certificates` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `structural-generalization-splits` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `dgt-base-undertraining-audit` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `input-accessibility` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `fair-l1-decision` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `discovery-gated-transformer` | `D0` | `` | `` | `source-insufficient` | `valid` | `reports/canonical/scaling-ladder.json:$.levels[0]` |
| `dgt-neural-ablation` | `D0` | `` | `` | `dgt-neural-ablation-pointer-only` | `valid` | `$.training_protocol` |
| `dgt-ablation-null-decomposition` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `dgt-component-redundancy-audit` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `dgt-model-card` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `order-k-benchmark` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `lejepa-theorem-ledger` | `D0` | `` | `` | `theorem-ledger-recorded` | `valid` | `$.theorem_rows` |
| `observed-debt-sweep` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `spectral-ablation-hinge` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[3]` |
| `model-comparison` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `causal-patch-suite` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `experiment-stack-cards` | `D0` | `` | `` | `source-insufficient` | `valid` | `source-insufficient` |
| `dimension-mismatch-debt-transfer` | `DN` | `` | `` | `projected` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[4]` |
| `single-threshold-escape` | `DN` | `` | `` | `escaped-positive-captured` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[5]` |
| `training-choice-observability` | `DN` | `` | `` | `pointer-only` | `valid` | `reports/canonical/negative_discovery_reports.json:$.rows[6]` |

## D5 readiness

### gap-head-on-h

- `threshold`: `pass` (reports/canonical/gap-head-robustness-sweep.json:$.A1_threshold_sweep.treatment_verdict.positive) A1 threshold sweep passes under the canonical robustness final_status.
- `ablation`: `failed` (reports/canonical/gap-head-ablation.json:$.hardgate.status) Gap-head ablation hardgate is explicit non-pass.
- `seed_expansion`: `pass` (reports/canonical/gap-head-robustness-sweep.json:$.A3_seed_expansion.final_verdict) A3 seed expansion has robust_positive final verdict under final_status=pass.
- `adversarial`: `pass` (reports/canonical/discovery_negative_witnesses.json:$.witnesses) The adversarial witness kinds do not break the discovery gate.
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
| `positive` | `DGT` | `reports/canonical/discovery-gated-transformer.json:$` | `pass` |
| `positive` | `DGT-neural-ablation` | `reports/canonical/dgt-neural-ablation.json:$` | `pass` |
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
