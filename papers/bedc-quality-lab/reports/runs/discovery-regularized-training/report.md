# Discovery-Regularized Training

- run_id: `discovery-regularized-training`
- schema_id: `bedc-quality-lab:discovery-regularized-training`
- discovery map signal: `d5-m-candidate`
- claim capsule: `reports/runs/discovery-regularized-training/claim_capsule.json`

## Hardgates

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

## Quality Promotion Boundary

- Owner pointer: `reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary`
- Slot state: `present-but-fail-closed`
- DRT-HG2 gate: `clears-boundary`
- Task-only quality_q: `0.581767`
- DRT quality_q CI-low: `0.607767`
- DRT minus task-only CI-low: `0.026`

| order | arm | quality_q | quality_q CI-low | comparison | gate | evidence |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `task_only` | `0.581767` | `0.581767` | `task-only-reference` | `reference` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.task_only` |
| 2 | `SIGReg` | `0.599767` | `0.599767` | `above-task-only` | `comparison-only` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.sigreg` |
| 3 | `DRT` | `0.641767` | `0.607767` | `above-task-only` | `clears-boundary` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.drt` |
| 4 | `matched_random_DRT` | `0.595767` | `0.595767` | `above-task-only` | `comparison-only` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.matched_random` |
| 5 | `old_certificate_guided` | `None` | `None` | `missing-evidence-fail-closed` | `fail-closed` | `reports/canonical/discovery-regularized-training.json:$.config.arms` |

## Mechanism Ablation

- status: `pass`
- raw rows: `reports/canonical/discovery-regularized-training.json:$.records.raw_rows_pointer`

| order | arm | quality_q | full minus ablation | full beats | parity |
| --- | --- | --- | --- | --- | --- |
| 1 | `without_discovery` | `0.632933` | `0.008834` | `True` | `False` |
| 2 | `without_ledger` | `0.627933` | `0.013834` | `True` | `False` |
| 3 | `without_certificate` | `0.622933` | `0.018834` | `True` | `False` |
| 4 | `without_mechanism` | `0.616933` | `0.024834` | `True` | `False` |
| 5 | `without_cost` | `0.636933` | `0.004834` | `True` | `False` |
| 6 | `without_negative_witness` | `0.629933` | `0.011834` | `True` | `False` |

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
- backend rows: `{'deterministic-anchor': 900, 'torch-training-arm': 16, 'deterministic-mechanism-ablation': 1}`
- total steps: `10992`
- wall time proxy seconds: `2.7`
- FLOPs proxy: `45023232`
- cost protocol pointer: `$.source_artifacts.cost_protocol`

## Not Claimed

- full model training
- global architecture superiority
- full LeJEPA reproduction
- mechanism closure
- production device authority
