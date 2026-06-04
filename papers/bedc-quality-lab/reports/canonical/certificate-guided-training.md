# Certificate-Guided Constraint Training

- Generated at: `2026-06-04T15:16:52.793015+00:00`
- Run id: `certificate-guided-constraint-training`
- Producer: `scripts/run_certificate_guided_constraint_training.py`
- Objective: `min L_task subject to UER <= alpha, Benefit >= beta, Debt <= gamma`
- Verdict: `DN(audit-improvement-tradeoff)`
- Failed gate: `audit-improvement-tradeoff`
- Claim capsule: `reports/runs/certificate-guided-constraint-training/claim_capsule.json`
- Grid summaries: `3402`
- Raw grid records: `27216`
- Raw metric records: `56`
- Raw metrics: `reports/runs/certificate-guided-constraint-training/raw_metrics.jsonl`
- Grid metrics: `reports/runs/certificate-guided-constraint-training/grid_metrics.jsonl`
- Grid summary records: `reports/runs/certificate-guided-constraint-training/grid_summary.jsonl`

## Arms

| arm | role | records | feasible grid records | delta debt | delta benefit | delta quality_q |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| `baseline` | `before` | 8 | 0 | 0.000000 | 0.000000 | 0.000000 |
| `debt_only` | `debt_only` | 8 | 729 | -0.050000 | -0.060800 | -0.035000 |
| `benefit_only` | `benefit_only` | 8 | 0 | 0.018000 | 0.023000 | -0.005000 |
| `debt_plus_benefit` | `debt_plus_benefit` | 8 | 891 | -0.064000 | -0.027050 | 0.020000 |
| `constraint_lagrangian` | `after` | 8 | 972 | -0.078000 | -0.009800 | 0.059000 |
| `constraint_lagrangian_adaptive_lambda` | `adaptive` | 8 | 972 | -0.070000 | 0.003000 | 0.066000 |
| `matched_random_debt` | `control` | 8 | 0 | -0.025000 | -0.015800 | -0.005000 |

## C1 Hardgates

- C1-HG1: `fail`
- C1-HG2: `fail`
- C1-HG3: `fail`
- C1-HG4: `pass`
- C1-HG5: `pass`

## Not Claimed

- lab-local constraint-training evidence only
- global model quality is not claimed
- full LeJEPA is not claimed
- full TensorNameCert is not claimed
- LLM behavior is not claimed
- mechanism closure is not claimed
- claim is falsifiable and revocable
- positive wording is not claimed for audit-improvement-tradeoff DN evidence
