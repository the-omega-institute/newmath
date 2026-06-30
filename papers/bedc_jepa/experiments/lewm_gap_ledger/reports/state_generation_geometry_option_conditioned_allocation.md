# State-Generation Geometry-Option Conditioned Allocation

- device: `cuda`
- selected epoch: `163`
- option feature dim: `5`
- geometry-option interaction dim: `80`

| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high | hard-only rho |
|---|---:|---:|---:|---:|---:|
| `geometry_option_conditioned` | 7.35549e-05 | -0.00623043 | 0.044361 | 0.0866947 | 0.824419 |
| `geometry_regime_weighted` | -0.00481929 | -0.00812573 | 0.0184095 | 0.0350834 | 0.349505 |
| `geometry_conditioned` | -0.0040868 | -0.00690023 | 0.0156785 | 0.0342666 | 0.348526 |
| `episode_best_seed` | -0.00359129 | -0.00792429 | 0.0268494 | 0.0372104 | 0.374175 |
| `episode_objective` | -0.00129762 | -0.005756 | 0.0300239 | 0.0417482 | 0.111917 |

## Verdict

Geometry-option conditioning does not improve the hard-only allocation boundary relative to the existing geometry rows.
