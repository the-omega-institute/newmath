# MiniGrid DoorKey Task Probe

- Generated at: `2026-06-16T00:00:00+00:00`
- Execution status: `abstain`
- Claim boundary: `bounded-negative`
- Preregistration digest: `8f9222877ca0421cf7c8c05223e05d165d6e8542df1136b6db82d9fe3f1ee78d`
- Base gate: `fail`
- Arms: `not-run`
- Hardgate: `fail`

## Hardgates

| gate | status | evidence |
| --- | --- | --- |
| `REAL` | `pass` | `$.dependency_status` |
| `BASE-CHANCE` | `fail` | `$.base_chance_gate` |
| `DATA` | `pass` | `$.data_surface` |
| `SEED` | `pass` | `$.preregistration.split_protocol` |
| `GAP` | `fail` | `$.arms.gap_head` |
| `DRT-REAL` | `fail` | `$.arms.drt` |
| `FAIR-INPUT` | `fail` | `$.control_protocol` |
| `FAIR-COMP` | `fail` | `$.control_protocol` |
| `HELDOUT` | `fail` | `$.arms.heldout` |
| `TRAIN` | `pass` | `$.training_evidence` |
| `STAT` | `fail` | `$.arms` |
| `REPRO` | `pass` | `$.reproducibility_contract` |

## Not Claimed

- No public MiniGrid benchmark superiority claim.
- No OOD generalization claim when heldout gates fail.
- No downstream gap-head or DRT claim when the base-chance gate fails.
- No production policy or robotics claim.
