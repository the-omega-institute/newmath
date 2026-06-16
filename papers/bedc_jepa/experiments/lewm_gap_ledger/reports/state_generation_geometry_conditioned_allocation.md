# State-Generation Geometry-Conditioned Allocation

- device: `cuda`
- selected epoch: `6`
- geometry feature dim: `16`

| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high |
|---|---:|---:|---:|---:|
| `geometry_conditioned` | -0.0040868 | -0.00690023 | 0.0156785 | 0.0349222 |
| `episode_best_seed` | -0.00359129 | -0.00792429 | 0.0268494 | 0.0376343 |
| `episode_objective` | -0.00129762 | -0.005756 | 0.0300239 | 0.041747 |
| `seed_mean` | -0.00280072 | -0.00836696 | 0.0363038 | 0.0579332 |

## Verdict

Geometry conditioning improves the hard-only observed allocation delta relative to the best replicated seed, but it does not close hard-only allocation.
