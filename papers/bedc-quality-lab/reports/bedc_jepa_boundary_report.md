# BEDC Model Quality Lab 报告

- 运行 ID：`boundary-gated-bedc-jepa-protocol-seed-41`
- Schema：`bedc-quality-lab:evidence-envelope`
- 数据源：`boundary-gated-ou-world`
- 模式：`latent-plus-distinction-plus-gap`
- 分类器：`bedc-jepa-protocol-radial-distinction-gap-heads`
- 稳定性设置：`ou-continuation-boundary-scope`

## 指标

- `approx_identifiability_proxy`：0.902705
- `bedc_debt_score`：0.177884
- `certified_coverage`：0.916667
- `covariance_deviation`：0.066069
- `distinction_accuracy`：0.881510
- `distinction_accuracy_outside_gap`：0.915254
- `false_claim_rate_inside_gap`：0.316667
- `gap_detection_auc`：0.783498
- `linear_identifiability_r2`：0.927453
- `orthogonality_error`：0.065958
- `unlogged_error_rate`：0.078125

## Ledger gaps

- no-gradient-bedc-jepa-training-yet
- one-boundary-family
- no-gap-aware-planning-rollout-yet

## Debt items

- model-debt: this artifact defines the BEDC-JEPA target protocol before training the full objective
- gap-debt: boundary-gated ledger is radial and synthetic only
- planning-debt: gap penalty theorem is specified in the directive but not experimentally tested here

## Artifacts

- `envelope`：`reports/bedc_jepa_boundary_envelope.json`
- `report`：`reports/bedc_jepa_boundary_report.md`

## BEDC refs

- `papers/bedc/preamble.tex:closurestatus`
- `papers/bedc/parts/project_governance/theory_amendment_policy.tex`
