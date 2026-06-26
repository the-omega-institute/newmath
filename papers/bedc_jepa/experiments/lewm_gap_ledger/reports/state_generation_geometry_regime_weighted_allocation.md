# State-Generation Geometry-Regime Weighted Allocation

- device: `cuda`
- selected epoch: `48`
- geometry feature dim: `16`
- agent-y threshold: `60.763`

| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high |
|---|---:|---:|---:|---:|
| `geometry_regime_weighted` | -0.00481929 | -0.00812573 | 0.0184095 | 0.0345351 |
| `geometry_conditioned` | -0.0040868 | -0.00690023 | 0.0156785 | 0.0349211 |
| `episode_best_seed` | -0.00359129 | -0.00792429 | 0.0268494 | 0.0375177 |
| `episode_objective` | -0.00129762 | -0.005756 | 0.0300239 | 0.042352 |
| `seed_mean` | -0.00280072 | -0.00836696 | 0.0363038 | 0.0571076 |

## Verdict

Train-defined geometry-regime weighting does not improve the hard-only allocation boundary relative to append-only geometry conditioning.
