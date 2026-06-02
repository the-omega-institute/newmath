# Canonical latent distribution observed-debt sweep

- Generated at: `2026-06-02T17:30:17.635409+00:00`
- Seed count: `6`
- Sample count: `384`
- Rho: `0.82`
- Main claim status: `observed-debt-pipeline-only`
- Not claimed: The report records observed latent-distribution debt for a finite toy setting and does not claim broad non-Gaussian failure.

## Coverage item

- Row: `source/distribution-family-coverage`
- Covered: `gaussian, laplace, uniform, student_t:3, generalized_normal:0.5, generalized_normal:1, generalized_normal:2, generalized_normal:4, generalized_normal:8`
- Missing: ``
- Status: `closed`
- Score: `0.000000`

## Distribution aggregates

| distribution | shape_parameter | linear_identifiability_r2 | actual_recovery_mse | theorem3_bound_mse | latent_distribution_debt | quality_q |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| `gaussian` | `None` | 0.926878 | 0.167679 | 0.796199 | 0.000000 | -0.085993 |
| `laplace` | `None` | 0.895408 | 0.219866 | 1.461414 | 0.160000 | -0.225487 |
| `uniform` | `None` | 0.965991 | 0.088767 | 1.299915 | 0.160000 | -0.146700 |
| `student_t` | `3.0` | 0.813578 | 3.606627 | 154.881915 | 0.160000 | -0.387300 |
| `generalized_normal` | `0.5` | 0.803488 | 0.809283 | 2.427884 | 0.160000 | -0.431268 |
| `generalized_normal` | `1.0` | 0.871144 | 0.352154 | 0.803160 | 0.160000 | -0.455919 |
| `generalized_normal` | `2.0` | 0.931022 | 0.158352 | 0.802536 | 0.160000 | -0.251048 |
| `generalized_normal` | `4.0` | 0.953192 | 0.106178 | 1.241197 | 0.160000 | -0.162461 |
| `generalized_normal` | `8.0` | 0.960619 | 0.092550 | 1.239360 | 0.160000 | -0.120071 |

## Claim gate

- Status: `observed-debt-pipeline-only`
- Minimum R2 drop: `0.01`
- Not claimed: Gaussian optimality is not asserted unless every non-Gaussian arm has a supported paired-bootstrap R2 drop.

| distribution_key | mean delta | ci95 | supports Gaussian optimality |
| --- | ---: | --- | --- |
| `laplace` | -0.031471 | `-0.044538, -0.011733` | `True` |
| `uniform` | 0.039112 | `0.032700, 0.046031` | `False` |
| `student_t:3` | -0.113300 | `-0.199031, -0.033820` | `True` |
| `generalized_normal:0.5` | -0.123390 | `-0.208446, -0.061696` | `True` |
| `generalized_normal:1` | -0.055734 | `-0.115392, -0.022902` | `True` |
| `generalized_normal:2` | 0.004143 | `-0.001455, 0.012786` | `False` |
| `generalized_normal:4` | 0.026314 | `0.022403, 0.031251` | `False` |
| `generalized_normal:8` | 0.033740 | `0.026292, 0.042199` | `False` |

## Negative-result ledger

| distribution_key | paired seeds | not claimed |
| --- | --- | --- |
| `laplace` | `5044` | This cell is not evidence for a Gaussian optimality claim. |
| `uniform` | `544, 1558, 2646, 3808, 5044, 6354` | This cell is not evidence for a Gaussian optimality claim. |
| `student_t:3` | `6354` | This cell is not evidence for a Gaussian optimality claim. |
| `generalized_normal:2` | `544, 1558, 2646, 3808, 5044, 6354` | This cell is not evidence for a Gaussian optimality claim. |
| `generalized_normal:4` | `544, 1558, 2646, 3808, 5044, 6354` | This cell is not evidence for a Gaussian optimality claim. |
| `generalized_normal:8` | `544, 1558, 2646, 3808, 5044, 6354` | This cell is not evidence for a Gaussian optimality claim. |
