# Canonical nonlinear mixing-family sweep

- Generated at: `2026-06-04T07:26:52.353351+00:00`
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
| `spiral` | 6 | `498, 1530, 2644, 3840, 5118, 6478` | 0.912362 | 0.844240 | -0.753001 | 1.000000 | 0.651594 |
| `sinusoidal_shear` | 6 | `498, 1530, 2644, 3840, 5118, 6478` | 0.928304 | 0.828541 | -0.740588 | 1.000000 | 0.516861 |
| `parabolic_shear` | 6 | `498, 1530, 2644, 3840, 5118, 6478` | 0.949566 | 0.884567 | -0.762280 | 1.000000 | 0.446312 |
| `realnvp_coupling` | 6 | `498, 1530, 2644, 3840, 5118, 6478` | 0.988679 | 0.875154 | -0.711832 | 1.000000 | 0.538850 |

## Negative-result audit

| family | quality_q delta vs spiral | negative result |
| --- | ---: | --- |
| `spiral` | 0.000000 | `False` |
| `sinusoidal_shear` | 0.012413 | `False` |
| `parabolic_shear` | -0.009279 | `True` |
| `realnvp_coupling` | 0.041168 | `False` |

## Applicability boundary

- Claimed scope: `Gaussian 2D latent + Gaussian OU transition + canonical nonlinear observation mixing families.`
- Not claimed: This sweep does not claim non-Gaussian latent coverage, non-Gaussian transition noise, or non-canonical mixing closure.
