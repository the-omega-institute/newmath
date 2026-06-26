# Gap-Head Transfer Atlas

- JSON artifact pointer: `reports/canonical/gap_head_transfer_atlas.json`
- Report artifact pointer: `reports/canonical/gap_head_transfer_atlas.md`
- Run id: `gap-head-transfer-atlas`
- Surface registry pointer: `$.surface_registry`
- Surface verdict nodes: `$.surfaces.<index>.verdict`
- Hardgate evidence pointer: `$.hardgate_evidence`
- Boundary ledger pointer: `$.boundary_ledger`
- Claim capsule pointer: `reports/runs/gap-head-transfer-atlas/claim_capsule.json`

## Decision

| field | value | pointer |
| --- | --- | --- |
| decision | `pass` | `$.multi_surface_d5_o.decision` |
| discovery level | `D5-O` | `$.multi_surface_d5_o.discovery_level` |
| pass surface count | `4` | `$.multi_surface_d5_o.pass_surface_count` |
| threshold | `3` | `$.multi_surface_d5_o.threshold` |

## Surfaces

| surface | kind | verdict | learned AUROC | matched AUROC | learned UER reduction | matched UER reduction |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| `clean_gaussian_ou` | `clean` | `failed` | 0.850812 | 0.511686 | 0.428885 | 0.375915 |
| `sample_count_1024` | `observed_debt` | `pass` | 0.826458 | 0.456616 | 0.399349 | 0.267101 |
| `sample_count_256` | `observed_debt` | `failed` | 0.794469 | 0.481994 | 0.355844 | 0.281818 |
| `anisotropic_rho_0p95_0p30` | `observed_debt` | `failed` | 0.847402 | 0.516002 | 0.427177 | 0.370789 |
| `anisotropic_rho_0p90_0p60` | `observed_debt` | `failed` | 0.849143 | 0.512666 | 0.427014 | 0.372091 |
| `laplace_latent` | `observed_debt` | `failed` | 0.717402 | 0.505001 | 0.313344 | 0.269243 |
| `student_t_df3_latent` | `observed_debt` | `failed` | 0.680087 | 0.502987 | 0.297559 | 0.220830 |
| `uniform_latent` | `observed_debt` | `pass` | 0.820872 | 0.441253 | 0.399024 | 0.279007 |
| `generalized_normal_alpha_0p5` | `observed_debt` | `failed` | 0.697115 | 0.510443 | 0.305940 | 0.245321 |
| `generalized_normal_alpha_4` | `observed_debt` | `pass` | 0.842263 | 0.544205 | 0.409927 | 0.321806 |
| `mixing_shift_spiral` | `observed_debt` | `failed` | 0.939942 | 0.547057 | 0.507323 | 0.535557 |
| `mixing_shift_realnvp` | `observed_debt` | `pass` | 0.969020 | 0.514072 | 0.480065 | 0.382587 |
| `optimizer_undertraining` | `observed_debt` | `failed` | 0.850812 | 0.511686 | 0.428885 | 0.375915 |

## Boundary Ledger

| surface | failed gates | pointers |
| --- | --- | --- |
| `clean_gaussian_ou` | `A2-HG2` | `A2-HG2: $.surfaces.0.hardgates.A2-HG2` |
| `sample_count_256` | `A2-HG2` | `A2-HG2: $.surfaces.2.hardgates.A2-HG2` |
| `anisotropic_rho_0p95_0p30` | `A2-HG2` | `A2-HG2: $.surfaces.3.hardgates.A2-HG2` |
| `anisotropic_rho_0p90_0p60` | `A2-HG2` | `A2-HG2: $.surfaces.4.hardgates.A2-HG2` |
| `laplace_latent` | `A2-HG2` | `A2-HG2: $.surfaces.5.hardgates.A2-HG2` |
| `student_t_df3_latent` | `A2-HG2` | `A2-HG2: $.surfaces.6.hardgates.A2-HG2` |
| `generalized_normal_alpha_0p5` | `A2-HG2` | `A2-HG2: $.surfaces.8.hardgates.A2-HG2` |
| `mixing_shift_spiral` | `A2-HG2, A2-HG3` | `A2-HG2: $.surfaces.10.hardgates.A2-HG2, A2-HG3: $.surfaces.10.hardgates.A2-HG3` |
| `optimizer_undertraining` | `A2-HG2` | `A2-HG2: $.surfaces.12.hardgates.A2-HG2` |

## Not Claimed

- lab-local multi-surface transfer evidence
- not global model quality
- not full LeJEPA
- not full TensorNameCert
- not LLM behavior
- not mechanism closure
- revocable under rerun or boundary expansion
