# BEDC Model Quality Lab 报告

- 运行 ID：`gaussian-ou-lejepa-seed-23`
- Schema：`bedc-quality-lab:evidence-envelope`
- 数据源：`gaussian-ou-toy-world`
- 模式：`latent-linear-recovery`
- 分类器：`tiny-mlp-2-128-128-2`
- 稳定性设置：`fixed-seed-single-source`

## 指标

- `approx_identifiability_proxy`：0.896834
- `covariance_deviation`：0.473880
- `linear_identifiability_r2`：0.957419
- `orthogonality_error`：0.005398

## Ledger gaps

- finite-sample-only
- single-mixing-family
- no-global-claim

## Debt items

- distribution-debt: only Gaussian latent source is exercised
- optimization-debt: tiny encoder training is not certified optimal
- stability-debt: one seed is committed as the canonical artifact

## Artifacts

- `envelope`：`reports/example_envelope.json`
- `report`：`reports/quality_report.md`

## BEDC refs

- `papers/bedc/preamble.tex:closurestatus`
- `papers/bedc/parts/project_governance/theory_amendment_policy.tex`
