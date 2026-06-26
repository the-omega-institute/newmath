# Phase 1b: LeWM gap ledger head on tworooms latent

- valid transitions: 642; episodes: 37
- split transitions: train=399, calibration=119, eval=124
- conclusion: **negative_or_inconclusive** - fail-closed: current eval bootstrap CI does not establish both required inequalities
- identifiability train mean R2: 0.9280; eval report-only mean R2: 0.2760
- native prediction_error threshold: prediction_mse > 1.086457 (train p75)

## Arm metrics (eval bootstrap 95% CI)

| arm | AUROC | ECE | UER | critical UER |
|---|---:|---:|---:|---:|
| vanilla | 0.5000 [0.5000, 0.5000] | 0.1365 [0.0516, 0.2171] | 0.3871 [0.3022, 0.4677] | 0.0000 [0.0000, 0.0000] |
| learned_gap_head_on_h | 0.5872 [0.4800, 0.6820] | 0.2127 [0.1692, 0.3260] | 0.2339 [0.1613, 0.3065] | 0.0242 [0.0000, 0.0645] |
| matched_random_gap_head | 0.4616 [0.3560, 0.5691] | 0.3179 [0.2511, 0.4139] | 0.2903 [0.2177, 0.3629] | 0.0403 [0.0119, 0.0806] |

## Distinction probe separability

| distinction | train rate | eval rate | train acc | eval acc |
|---|---:|---:|---:|---:|
| agent_room_right | 0.5138 | 0.3306 | 1.0000 | 0.9919 |
| same_room | 0.2632 | 0.3306 | 0.8546 | 0.5000 |
| near_target | 0.4987 | 0.7177 | 0.8421 | 0.5806 |

## Prediction-error definitions

- native latent-error eval rate: 0.3871
- Loning probe-error eval rate: 0.7016
- native/probe agreement eval: 0.4758

## Off-target intervention

- status: computed_with_lewm_predictor
- label rate all rows: 0.7632398753894081

## Debt

- coverage_debt / statistical_design: single LeWM tworooms latent export with 37 episodes/642 transitions; bootstrap CI does not replace >=30 independent world seeds
- source_debt / distinction_probe:same_room: eval accuracy 0.5000 below 0.60 separability sanity threshold
- source_debt / distinction_probe:near_target: eval accuracy 0.5806 below 0.60 separability sanity threshold

Full gap_sound_scan grids and per-arm calibration metrics are in `reports/lewm_gap_ledger_head.json`.
