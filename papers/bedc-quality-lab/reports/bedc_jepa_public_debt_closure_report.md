# BEDC-JEPA Public Debt Closure Report

## Question

Public MiniGrid reduces silent failures and improves gap ranking, but aggregate debt is not fully closed.

## Debt Decomposition

- S0 silent debt: `0.065625`
- S3 silent debt: `0.015625`
- S0 coverage debt: `0.000000`
- S3 coverage debt: `0.065625`
- S0 total debt: `0.165625`
- S3 total debt: `0.163102`
- Diagnosis: `silent debt falls while coverage debt rises`

## Certified Coverage

- Best S3 gap threshold: `0.80`
- Best S3 debt: `0.141227`
- Best S3 certified coverage: `1.000000`

## Conformal Certified Claims

- DoorKey context coverage at alpha 0.20: `0.468750`
- DoorKey context UER at alpha 0.20: `0.046875`
- Predicate surfaces: `door_key_context_visible`, `has_key`, `door_open_or_unlocked`, `goal_reachable_with_current_state`, `unsafe_transition`

## Risk-Constrained Planning

- Rule: select the highest distinction score among actions whose predicted gap is within the risk budget; if no such action exists, record `no_certified_plan`.
- Selected risk budget: `0.10`
- Claim status: `risk_success_tradeoff` at the tightest recorded budget
- High-gap state rate: `0.000000`
- Effective success rate: `0.093750`
- No-certified-plan rate: `0.906250`
- Pareto half-risk success: `0.781250`

## Local Ablation

- Unlogged-penalty effect: `0.085938`
- Post-hoc gap debt delta: `0.015670`
- Boundary: `local score ablation; not a retraining ablation`

## Not Claimed

- public benchmark superiority
- closed total debt on all public MiniGrid seeds
- native V-JEPA2-AC checkpoint reproduction
- optimal planning calibration
