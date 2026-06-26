# State-Generation Episode Assignment Value

- selected priority seed row: `base_plus_0.5_residual`
- selected epoch: `22`

| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high | hard-only oracle match |
|---|---:|---:|---:|---:|---:|
| `episode_assignment_value` | -0.00328615 | -0.00813263 | 0.0307619 | 0.0717705 | 0.189873 |
| `priority_residual` | -0.00429771 | -0.00420687 | -0.0049359 | 0.00445217 | 0.139241 |
| `base_geometry_option` | -0.00373002 | -0.00348872 | -0.00542522 | 0.00465595 | 0.139241 |

## Verdict

Episode-aware assignment-value scorer does not improve the hard-only allocation boundary over the raw geometry-option scorer.
