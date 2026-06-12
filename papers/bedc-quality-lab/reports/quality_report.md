# BEDC Model Quality Lab 报告

- 运行 ID：`gaussian-ou-lejepa-seed-23`
- Schema：`bedc-quality-lab:evidence-envelope`
- 数据源：`gaussian-ou-toy-world`
- 模式：`latent-linear-recovery`
- 分类器：`tiny-mlp-2-128-128-2`
- 稳定性设置：`fixed-seed-single-source`

## Tensor NameCert Candidate

- Candidate：`TensorNameCertCandidate:gaussian-ou-lejepa-seed-23`
- Evidence envelope：`bedc-quality-lab:evidence-envelope:gaussian-ou-lejepa-seed-23`
- `source_spec` lab-local candidate closure：`closed`
- `pattern_spec` lab-local candidate closure：`closed`
- `classifier_spec` lab-local candidate closure：`closed`
- `stab_cert` stability lab-local candidate closure：`closed`
- `ledger_policy` lab-local candidate closure：`partial`
- `scope_seal` lab-local candidate closure：`closed`
- Scope seal：`lab-local candidate projection`

## 指标

- `approx_identifiability_proxy`：0.795744
- `covariance_deviation`：0.685355
- `linear_identifiability_r2`：0.910984
- `orthogonality_error`：0.118285

## Identifiability Bound: MSE Scale

- `cert_status`：`certified`
- `alignment_loss_mse`：0.586177
- `covariance_trace`：1.064348
- `alignment_gap_delta_mse`：0.203012
- `normalized_gap_d_mse`：0.687709
- `whitening_deviation_epsilon`：0.685355
- `theorem3_bound_mse`：2.573014
- `actual_recovery_mse`：0.311029
- `bound_margin_mse`：2.261984
- `theorem_bound_benefit`：0.535853
- `theorem_bound_gap_penalty`：0.687709
- `theorem_bound_whitening_penalty`：0.685355
- `theorem_bound_recovery_pressure`：0.120881

## Normalized Projection

- `alignment_loss_normalized`：0.293088
- `alignment_gap_delta_normalized`：0.000000
- `actual_recovery_normalized`：0.147478
- `theorem3_bound_normalized`：2.417457
- `bound_margin_normalized`：2.269979

## Q 投影

- `quality_benefit`：0.535853
- `quality_cost`：0.060000
- `quality_debt`：0.800000
- `quality_margin`：-0.324147
- `quality_q`：-0.324147
- `quality_threshold`：0.000000

## Cost Protocol

- Protocol: `bedc-quality-lab-default-cost-protocol`
- Formula: `quality_q` = `quality_benefit - quality_cost - quality_debt`
- Row weights:
  - `classifier/optimizer-certificate`: 0.200000
  - `generalization/global-claim-boundary`: 0.200000
  - `source/finite-sample-support`: 0.200000
  - `source/mixing-family-coverage`: 0.220000
  - `source/source-coverage`: 0.180000
  - `source/transition-isotropy`: 0.120000
  - `verification/theorem3-bound-margin`: 0.200000
- Not claimed global boundary:
  - tokens: `outside-declared-scope`, `untested-source-families`, `unproved-global-generalization`
  - treatment: Claims outside these boundary tokens are not included in quality_q closure credit.

## Ledger gaps

- kind=classifier; residue=optimizer-certificate; severity=high; status=open
- kind=source; residue=finite-sample-support; severity=high; status=open
- kind=source; residue=mixing-family-coverage; severity=high; status=open
- kind=source; residue=source-coverage; severity=high; status=open

## Debt items

- kind=source; residue=source-coverage; severity=high; status=open; score=0.180000
- kind=source; residue=mixing-family-coverage; severity=high; status=open; score=0.220000
- kind=source; residue=finite-sample-support; severity=high; status=open; score=0.200000
- kind=source; residue=transition-isotropy; severity=none; status=closed; score=0.000000
- kind=classifier; residue=optimizer-certificate; severity=high; status=open; score=0.200000
- kind=verification; residue=theorem3-bound-margin; severity=none; status=closed; score=0.000000
- kind=generalization; residue=global-claim-boundary; severity=none; status=closed; score=0.000000

## Artifacts

- `envelope`：`reports/example_envelope.json`
- `report`：`reports/quality_report.md`

## BEDC refs

- `papers/bedc/preamble.tex:closurestatus`
- `papers/bedc/parts/project_governance/theory_amendment_policy.tex`
