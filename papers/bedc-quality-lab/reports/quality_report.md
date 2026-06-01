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

## Q 投影

- `quality_benefit`：0.927126
- `quality_cost`：0.060000
- `quality_debt`：0.800000
- `quality_margin`：0.067126
- `quality_q`：0.067126
- `quality_threshold`：0.000000

## Ledger gaps

- kind=classifier; residue=optimizer-certificate; severity=high; status=open
- kind=source; residue=finite-sample-support; severity=high; status=open
- kind=source; residue=mixing-family-coverage; severity=high; status=open
- kind=source; residue=source-coverage; severity=high; status=open

## Debt items

- kind=source; residue=source-coverage; severity=high; status=open; score=0.180000
- kind=source; residue=mixing-family-coverage; severity=high; status=open; score=0.220000
- kind=source; residue=finite-sample-support; severity=high; status=open; score=0.200000
- kind=classifier; residue=optimizer-certificate; severity=high; status=open; score=0.200000
- kind=generalization; residue=global-claim-boundary; severity=none; status=closed; score=0.000000

## Artifacts

- `envelope`：`reports/example_envelope.json`
- `report`：`reports/quality_report.md`

## BEDC refs

- `papers/bedc/preamble.tex:closurestatus`
- `papers/bedc/parts/project_governance/theory_amendment_policy.tex`
