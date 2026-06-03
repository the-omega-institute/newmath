# Certificate Constraint Frontier

- Source JSON artifact: `reports/certificate_guided_training.json`
- Projection script: `scripts/run_certificate_constraint_frontier.py`
- Local schema id: `bedc-quality-lab:certificate-constraint-frontier-sidecar`
- Sidecar role: `pointer_only_non_canonical`
- Canonical status: `sidecar_not_canonical`
- Constraint form: `min task_loss subject to UER<=alpha, Benefit>=beta, Debt<=gamma`
- Hardgate status: `non-positive`
- Failed gate: `audit-improvement-tradeoff`
- Positive pointer: `false`
- Feasible frontier cells: `38`
- Not claimed: `formal BEDC closure is not claimed by this sidecar; global optimizer behavior is not claimed by this sidecar; universal certificate-guided improvement is not claimed by this sidecar; positive discovery is not claimed for a debt-down benefit-down tradeoff; schema or canonical report status is not claimed by this sidecar`

## Threshold Sources

- Alpha: observed UER quantiles from `$.records[*].unlogged_error_rate`.
- Beta: baseline benefit plus candidate benefit bands from `$.records[*].quality_benefit`.
- Gamma: baseline debt plus candidate debt bands from `$.records[*].quality_debt`.
- No hidden cost weight, total score, rank, or grade is produced.

## Frontier Preview

| threshold | alpha | beta | gamma | status | candidate | task_loss |
| --- | ---: | ---: | ---: | --- | --- | ---: |
| `ccf-000-000` | 0.026087 | 0.080745 | 0.950901 | `constraint-satisfied local candidate` | `debt_only` | 0.073249 |
| `ccf-000-001` | 0.026087 | 0.080745 | 0.975450 | `constraint-satisfied local candidate` | `debt_only` | 0.073249 |
| `ccf-000-002` | 0.026087 | 0.080745 | 1.000000 | `constraint-satisfied local candidate` | `debt_only` | 0.073249 |
| `ccf-000-003` | 0.026087 | 0.080745 | 1.000000 | `constraint-satisfied local candidate` | `debt_only` | 0.073249 |
| `ccf-000-004` | 0.026087 | 0.191527 | 0.950901 | `infeasible` | `none` | `none` |
| `ccf-000-005` | 0.026087 | 0.191527 | 0.975450 | `infeasible` | `none` | `none` |
| `ccf-000-006` | 0.026087 | 0.191527 | 1.000000 | `infeasible` | `none` | `none` |
| `ccf-000-007` | 0.026087 | 0.191527 | 1.000000 | `infeasible` | `none` | `none` |
| `ccf-000-008` | 0.026087 | 0.309785 | 0.950901 | `infeasible` | `none` | `none` |
| `ccf-000-009` | 0.026087 | 0.309785 | 0.975450 | `infeasible` | `none` | `none` |
| `ccf-000-010` | 0.026087 | 0.309785 | 1.000000 | `infeasible` | `none` | `none` |
| `ccf-000-011` | 0.026087 | 0.309785 | 1.000000 | `infeasible` | `none` | `none` |

## Dominance

| arm | task_loss_delta | uer_delta | benefit_delta | debt_delta | positive |
| --- | ---: | ---: | ---: | ---: | --- |
| `baseline` | 0.000000 | 0.000000 | 0.000000 | 0.000000 | `false` |
| `debt_only` | 0.003497 | -0.471739 | -0.229040 | -0.049099 | `false` |
| `benefit_only` | 0.000000 | 0.000000 | 0.000000 | 0.000000 | `false` |
| `debt_plus_benefit` | 0.003497 | -0.471739 | -0.229040 | -0.049099 | `false` |
| `matched_random_debt` | 0.236069 | 0.000000 | -0.007476 | 0.000000 | `false` |

## HG-CCF

- HG-CCF-1: `fail`
- HG-CCF-2: `pass`
- HG-CCF-3: `pass`
- HG-CCF-4: `fail`
- HG-CCF-5: `pass`
- HG-CCF-6: `pass`
