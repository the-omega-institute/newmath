# Discovery-Regularized Training

- run_id: `discovery-regularized-training`
- schema_id: `bedc-quality-lab:discovery-regularized-training`
- discovery map signal: `d5-m-candidate`
- claim capsule: `reports/runs/discovery-regularized-training/claim_capsule.json`

## Hardgates

- `DGT-REPLAY-HG0-owner-ready`: `pass`
- `DGT-REPLAY-HG1`: `pass`
- `DGT-REPLAY-HG2`: `pass`
- `DGT-REPLAY-HG3`: `pass`
- `DGT-REPLAY-HG4`: `pass`
- `DGT-REPLAY-HG5`: `pass`
- `DGT-REPLAY-HG6`: `pass`
- `DGT-REPLAY-HG7`: `pass`
- `DGT-REPLAY-HG8`: `pass`
- `DGT-REPLAY-HG9`: `pass`
- `DGT-REPLAY-HG10`: `pass`
- `DRT-HG1`: `pass`
- `DRT-HG2`: `pass`
- `DRT-HG3`: `pass`
- `DRT-HG4`: `pass`
- `DRT-HG5`: `pass`
- `DRT-HG6`: `pass`
- `DRT-HG7`: `pass`
- `DRT-HG8`: `pass`
- `DRT-HG9`: `pass`
- `DRTJ-HG1`: `pass`
- `DRTJ-HG2`: `pass`
- `DRTJ-HG3`: `pass`
- `DRTJ-HG4`: `pass`
- `DRTJ-HG5`: `pass`

## DGT Replay

- status: `pass`
- failed gate: `None`
- comparison owner: `ready`

| order | arm | role | UER | false ledger rate | shift |
| --- | --- | --- | --- | --- | --- |
| 1 | `base_transformer` | `model-comparison:base_transformer` | `0.256067` | `0.167` | `0.0` |
| 2 | `parameter_matched` | `parameter-matched control` | `0.186067` | `0.167` | `0.0` |
| 3 | `compute_matched` | `compute-matched control` | `0.252067` | `0.167` | `0.0` |
| 4 | `matched_random_structural_control` | `model-comparison:matched_random_structural_control` | `0.216067` | `0.367` | `0.0` |
| 5 | `DGT_full` | `model-comparison:dgt` | `0.104067` | `0.167` | `1.0` |
| 6 | `DGT_without_LAT` | `DGT component ablation` | `0.133067` | `0.177` | `1.0` |
| 7 | `DGT_without_CGA` | `DGT component ablation` | `0.137067` | `0.177` | `1.0` |
| 8 | `DGT_without_DRT` | `DGT component ablation` | `0.229067` | `0.177` | `0.0` |
| 9 | `DGT_without_gap_ledger_route` | `DGT component ablation` | `0.253067` | `0.177` | `0.0` |
| 10 | `DGT_without_mechanism_probe` | `DGT component ablation` | `0.257067` | `0.177` | `0.0` |
| 11 | `DGT_without_certificate_gate` | `DGT component ablation` | `0.255067` | `0.177` | `0.0` |
| 12 | `DGT_without_jet_loss` | `DGT component ablation` | `0.120067` | `0.177` | `1.0` |

## Quality Promotion Boundary

- Owner pointer: `reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary`
- Slot state: `present-but-fail-closed`
- DRT-HG2 gate: `clears-boundary`
- Task-only quality_q: `0.581767`
- DRT quality_q CI-low: `0.607767`
- DRT minus task-only CI-low: `0.026`

| order | arm | quality_q | quality_q CI-low | comparison | gate | evidence |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `base_transformer` | `0.581767` | `0.581767` | `task-only-reference` | `reference` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.base_transformer` |
| 2 | `parameter_matched` | `0.599767` | `0.599767` | `above-task-only` | `comparison-only` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.parameter_matched` |
| 3 | `DGT_full` | `0.654767` | `0.607767` | `above-task-only` | `clears-boundary` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.DGT_full` |
| 4 | `matched_random_structural_control` | `0.595767` | `0.595767` | `above-task-only` | `comparison-only` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.matched_random_structural_control` |
| 5 | `old_certificate_guided` | `None` | `None` | `missing-evidence-fail-closed` | `fail-closed` | `reports/canonical/discovery-regularized-training.json:$.config.arms` |

## Mechanism Ablation

- status: `pass`
- raw rows: `reports/canonical/discovery-regularized-training.json:$.records.raw_rows_pointer`

| order | arm | quality_q | full minus ablation | full beats | parity |
| --- | --- | --- | --- | --- | --- |
| 1 | `without_discovery` | `0.645933` | `0.008834` | `True` | `False` |
| 2 | `without_ledger` | `0.640933` | `0.013834` | `True` | `False` |
| 3 | `without_certificate` | `0.635933` | `0.018834` | `True` | `False` |
| 4 | `without_mechanism` | `0.629933` | `0.024834` | `True` | `False` |
| 5 | `without_cost` | `0.649933` | `0.004834` | `True` | `False` |
| 6 | `without_negative_witness` | `0.642933` | `0.011834` | `True` | `False` |

## Training Mechanism Certificate

- status: `pass`
- owner pointer: `reports/canonical/discovery-regularized-training.json:$.training_mechanism_cert`
- hardgate pointer: `reports/canonical/discovery-regularized-training.json:$.hardgate.gates.DRT-HG9`
- required pointers resolve: `True`

## DRT Extension Hardgates

- `DRT-EXT-HG1_required_pointer_resolution`: `pass`
- `DRT-EXT-HG2_uer_threshold`: `pass`
- `DRT-EXT-HG3_component_ablation`: `pass`
- `DRT-EXT-HG4_forbidden_key_audit`: `pass`

## Jet Loss Surface

- status: `pass`
- owner pointer: `reports/canonical/discovery-regularized-training.json:$.jet_loss_surface`
- required order: `3`
- matched-random jet gain: `-0.003867`
- quality_q CI-low: `0.018`

| gate | status | evidence |
| --- | --- | --- |
| `DRTJ-HG1` | `pass` | `$.jet_loss_surface.metrics.drt_jet_minus_drt_required_order_gain` |
| `DRTJ-HG2` | `pass` | `$.jet_loss_surface.metrics.drt_jet_minus_drt_order_one_gain` |
| `DRTJ-HG3` | `pass` | `$.jet_ablation.shortcut_control_not_reducible` |
| `DRTJ-HG4` | `pass` | `$.jet_loss_surface.metrics.matched_random_jet_gain` |
| `DRTJ-HG5` | `pass` | `$.jet_loss_surface.metrics.quality_q_ci_low` |

## Jet Sidecars

- jet loss surface: `reports/canonical/discovery_regularized_training_jet.json`
- jet ablation: `reports/canonical/drt_jet_ablation.md`
- jet frontier: `reports/canonical/jet_loss_frontier.json`

## Device Protocol

- requested: `auto`
- resolved: `mps`
- status: `available`

## Compute Ledger

- status: `complete`
- backend rows: `{'deterministic-anchor': 2160, 'torch-training-arm': 16, 'deterministic-mechanism-ablation': 1}`
- total steps: `26112`
- wall time proxy seconds: `6.48`
- FLOPs proxy: `106954752`
- cost protocol pointer: `$.source_artifacts.cost_protocol`

## Not Claimed

- full model training
- global architecture superiority
- full LeJEPA reproduction
- mechanism closure
- production device authority
