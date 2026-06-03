# Gap-Head Multi-Surface Debt Transfer

- JSON artifact pointer: `runs/gap_head_multisurface_debt_transfer.json`
- Report artifact pointer: `runs/gap_head_multisurface_debt_transfer.md`
- Artifact id pointer: `$.artifact_id`
- Transfer status pointer: `$.gap_head_multisurface_debt_transfer.multi_surface_status`
- Surface registry pointer: `$.surface_registry`
- Surface verdict pointer: `$.surfaces[*].verdict`
- Hardgate evidence pointer: `$.hardgate_evidence`
- Boundary ledger pointer: `$.boundary_ledger`
- Mechanism status: `not_claimed`
- D5-M status: `not_claimed`

## Status

| field | value | pointer |
| --- | --- | --- |
| multi-surface status | `pass` | `$.gap_head_multisurface_debt_transfer.multi_surface_status` |
| pass surface count | `3` | `$.gap_head_multisurface_debt_transfer.pass_surface_count` |
| countable surface count | `4` | `$.gap_head_multisurface_debt_transfer.countable_surface_count` |

## Countable Surfaces

| surface | verdict | learned AUROC mean | matched-random AUROC mean | pointer |
| --- | --- | ---: | ---: | --- |
| `clean-gaussian-ou` | `pass` | 0.850812 | 0.511686 | `$.surfaces[*]` |
| `anisotropic-rho-0p95-0p30` | `pass` | 0.847402 | 0.516002 | `$.surfaces[*]` |
| `laplace-latent` | `failed` | 0.717402 | 0.505001 | `$.surfaces[*]` |
| `sample-count-1024` | `pass` | 0.826458 | 0.456616 | `$.surfaces[*]` |

## Boundary Ledger

| surface | kind | pointer |
| --- | --- | --- |
| `student-t-latent` | `deferred` | `bedc_quality_lab.latent_distribution.LatentDistributionSpec.student_t` |
| `realnvp-spiral-mixing` | `boundary_only` | `bedc_quality_lab.mixing.mix_latents` |
| `undertrain-boundary` | `not_runnable` | `scripts/run_gap_head_observed_debt_transfer.py::_boundary_ledger` |

## Not Claimed

- no mechanism closure claim
- no D5-M promotion
- no global quality conclusion
- no full LeJEPA conclusion
- no claim outside the listed countable runnable surfaces
- no inference-time use of z, z_pair, gap_label, prediction_error, or eval_gap_labels
