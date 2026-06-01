# Anisotropic Gaussian-OU transition-isotropy sweep

- Generated at: `2026-06-01T22:30:33.502883+00:00`
- Seed count: `20`
- Sample count: `384`
- Applicability boundary: `Gaussian latent + anisotropic transition`
- Transition noise family: `gaussian`
- Non-Gaussian transition noise: not claimed

## Transition debt by grid

| rho_by_axis | isotropic | anisotropy gap | transition debt mean | status | quality_q mean |
| --- | --- | ---: | ---: | --- | ---: |
| `(0.9, 0.9)` | `True` | 0.000000 | 0.000000 | closed | -0.624143 |
| `(0.9, 0.6)` | `False` | 0.300000 | 0.072000 | open-or-partial | -0.741402 |
| `(0.95, 0.3)` | `False` | 0.650000 | 0.120000 | open-or-partial | -0.808326 |
| `(0.99, 0.5)` | `False` | 0.490000 | 0.117600 | open-or-partial | -0.814645 |

## Negative-result audit

| rho_by_axis | quality_q delta vs isotropic | negative result |
| --- | ---: | --- |
| `(0.9, 0.9)` | 0.000000 | `False` |
| `(0.9, 0.6)` | -0.117259 | `True` |
| `(0.95, 0.3)` | -0.184183 | `True` |
| `(0.99, 0.5)` | -0.190502 | `True` |

## Applicability boundary

- Claimed scope: `Gaussian latent + anisotropic transition`
- Not claimed: This sweep does not claim non-Gaussian transition noise or non-Gaussian latent coverage.
- Eigenvalue interleaving summaries are copied from the JSON evidence payload.

| eigenvalues | anisotropy gap | min adjacent gap |
| --- | ---: | ---: |
| `(0.9, 0.9)` | 0.000000 | 0.000000 |
| `(0.9, 0.6)` | 0.300000 | 0.300000 |
| `(0.95, 0.3)` | 0.650000 | 0.650000 |
| `(0.99, 0.5)` | 0.490000 | 0.490000 |
