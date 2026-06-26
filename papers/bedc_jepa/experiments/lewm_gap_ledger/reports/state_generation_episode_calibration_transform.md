# State-Generation Episode Calibration Transform

- selected transform: `anchor_centered_gamma_0.5`
- raw score source: `deterministic fi-064 geometry-option scorer regenerated with the same seed/config`

| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high | hard-only rho |
|---|---:|---:|---:|---:|---:|
| `calibrated` | 7.35549e-05 | -0.00623043 | 0.044361 | 0.0906422 | 0.751162 |
| `base_geometry_option` | 7.35549e-05 | -0.00623043 | 0.044361 | 0.0894712 | 0.824419 |
| `geometry_conditioned` | -0.0040868 | -0.00690023 | 0.0156785 | 0.0343227 | 0.348526 |
| `geometry_regime_weighted` | -0.00481929 | -0.00812573 | 0.0184095 | 0.0355485 | 0.349505 |

## Verdict

Calibration transform does not improve the hard-only allocation boundary relative to the raw geometry-option scorer.
