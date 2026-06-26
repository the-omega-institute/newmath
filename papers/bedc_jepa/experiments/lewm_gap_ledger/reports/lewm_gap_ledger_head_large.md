# Phase 1c: expanded LeWM gap ledger head

- latent: `tworooms_latent_large.npz`; valid transitions: 4991; episodes: 278
- export: 2048 MiB H5 prefix, compressed read 558.39 MiB, prefix 47.70s, encode/predict 189.11s
- split transitions: train=3045, calibration=982, eval=964; eval episodes=55
- conclusion: **positive** - denoised learned gap head significantly beats matched-random on native prediction-error AUROC and beats vanilla on UER
- identifiability train mean R2: 0.8381; eval report-only mean R2: 0.7912
- native prediction_error threshold: prediction_mse > 0.076702 (train p75)

## Primary Tests

- B learned AUROC CI lower > B matched-random AUROC CI upper: True
- B learned UER CI upper < vanilla UER CI lower: True

## Arm metrics (eval episode-bootstrap 95% CI)

| arm | AUROC | ECE | UER | critical UER |
|---|---:|---:|---:|---:|
| vanilla | 0.5000 [0.5000, 0.5000] | 0.0186 [0.0017, 0.0452] | 0.2313 [0.2047, 0.2585] | 0.0000 [0.0000, 0.0000] |
| learned_gap_head_A_all_probe_features | 0.7322 [0.6877, 0.7719] | 0.0312 [0.0243, 0.0622] | 0.1701 [0.1485, 0.1942] | 0.0519 [0.0385, 0.0668] |
| matched_random_gap_head_A_all_probe_features | 0.5574 [0.5160, 0.6039] | 0.0411 [0.0214, 0.0677] | 0.2293 [0.2045, 0.2575] | 0.0166 [0.0102, 0.0233] |
| learned_gap_head_B_denoised_agent_room_only | 0.7314 [0.6923, 0.7745] | 0.0336 [0.0248, 0.0614] | 0.1680 [0.1423, 0.1912] | 0.0425 [0.0288, 0.0549] |
| matched_random_gap_head_B_denoised_agent_room_only | 0.4721 [0.4272, 0.5177] | 0.0846 [0.0609, 0.1120] | 0.2313 [0.2048, 0.2585] | 0.0259 [0.0166, 0.0368] |

## A/B Control

- A uses all probe features: ['agent_room_right', 'same_room', 'near_target']
- B removes Phase 1b source-debt probes (`same_room`, `near_target`) and keeps: ['agent_room_right']
- prediction_error AUROC delta B-A: -0.0008

## Distinction probe separability

| distinction | train rate | eval rate | train acc | eval acc |
|---|---:|---:|---:|---:|
| agent_room_right | 0.4624 | 0.5052 | 0.9990 | 1.0000 |
| same_room | 0.2759 | 0.2863 | 0.7310 | 0.6878 |
| near_target | 0.4998 | 0.5685 | 0.6361 | 0.5902 |

## Prediction-error definitions

- native latent-error eval rate: 0.2313
- Loning probe-error eval rate: 0.5840
- native/probe agreement eval: 0.4440

## Off-target intervention

- status: computed_with_lewm_predictor
- label rate all rows: 0.6237227008615508

## Debt

- coverage_debt / statistical_design: single LeWM tworooms latent export with 278 episodes/4991 transitions; episode bootstrap does not replace >=30 independent world seeds
- source_debt / distinction_probe:near_target: eval accuracy 0.5902 below 0.60 separability sanity threshold

Full gap_sound_scan grids and per-arm calibration metrics are in `reports/lewm_gap_ledger_head_large.json`.
