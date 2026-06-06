# Discovery-Regularized Training

- run_id: `discovery-regularized-training`
- schema_id: `bedc-quality-lab:discovery-regularized-training`
- discovery map signal: `d4-candidate`
- claim capsule: `reports/runs/discovery-regularized-training/claim_capsule.json`

## Hardgates

- `DRT-HG1`: `pass`
- `DRT-HG2`: `pass`
- `DRT-HG3`: `pass`
- `DRT-HG4`: `pass`
- `DRT-HG5`: `pass`
- `DRT-HG6`: `pass`

## Quality Promotion Boundary

- Owner pointer: `reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary`
- Slot state: `present-but-fail-closed`
- DRT-HG2 gate: `clears-boundary`
- Task-only quality_q: `0.581767`
- DRT quality_q CI-low: `0.585267`
- DRT minus task-only CI-low: `0.0035`

| order | arm | quality_q | quality_q CI-low | comparison | gate | evidence |
| --- | --- | --- | --- | --- | --- | --- |
| 1 | `task_only` | `0.581767` | `0.581767` | `task-only-reference` | `reference` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.task_only` |
| 2 | `SIGReg` | `0.599767` | `0.599767` | `above-task-only` | `comparison-only` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.sigreg` |
| 3 | `DRT` | `0.641767` | `0.585267` | `above-task-only` | `clears-boundary` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.drt` |
| 4 | `matched_random_DRT` | `0.595767` | `0.595767` | `above-task-only` | `comparison-only` | `reports/canonical/discovery-regularized-training.json:$.surface_registry.quality.by_arm.matched_random` |
| 5 | `old_certificate_guided` | `None` | `None` | `missing-evidence-fail-closed` | `fail-closed` | `reports/canonical/discovery-regularized-training.json:$.config.arms` |

## Device Protocol

- requested: `auto`
- resolved: `mps`
- status: `available`

## Not Claimed

- full model training
- global architecture superiority
- full LeJEPA reproduction
- mechanism closure
- production device authority
