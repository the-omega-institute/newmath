# Canonical nonlinear mixing-family sweep

- Generated at: `2026-06-01T22:41:20.846355+00:00`
- Seed count: `6`
- Seed floor: `6`
- Sample count: `384`
- Rho: `0.82`
- Families: `spiral, sinusoidal_shear, parabolic_shear, realnvp_coupling`
- Runner mode: `use_torch=False`

## Coverage item

- Row: `source/mixing-family-coverage`
- Covered: `spiral, sinusoidal_shear, parabolic_shear, realnvp_coupling`
- Missing: ``
- Status: `closed`
- Score: `0.000000`

## Family aggregates

| family | ok count | seeds | linear R2 mean | proxy mean | quality_q mean | debt mean | bound margin mean |
| --- | ---: | --- | ---: | ---: | ---: | ---: | ---: |
| `spiral` | 6 | `498, 1530, 2644, 3840, 5118, 6478` | 0.912318 | 0.839794 | -0.602129 | 0.706862 | 0.243381 |
| `sinusoidal_shear` | 6 | `498, 1530, 2644, 3840, 5118, 6478` | 0.928773 | 0.830248 | -0.611367 | 0.705207 | 0.185774 |
| `parabolic_shear` | 6 | `498, 1530, 2644, 3840, 5118, 6478` | 0.950357 | 0.880197 | -0.677301 | 0.708618 | 0.098046 |
| `realnvp_coupling` | 6 | `498, 1530, 2644, 3840, 5118, 6478` | 0.988590 | 0.875120 | -0.522156 | 0.703211 | 0.330665 |

## Negative-result audit

| family | quality_q delta vs spiral | negative result |
| --- | ---: | --- |
| `spiral` | 0.000000 | `False` |
| `sinusoidal_shear` | -0.009238 | `True` |
| `parabolic_shear` | -0.075172 | `True` |
| `realnvp_coupling` | 0.079973 | `False` |

## Applicability boundary

- Claimed scope: `Gaussian 2D latent + Gaussian OU transition + canonical nonlinear observation mixing families.`
- Not claimed: This sweep does not claim non-Gaussian latent coverage, non-Gaussian transition noise, or non-canonical mixing closure.
