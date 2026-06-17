# State-Generation Residual Benefit Selector

- selected scorer: `priority_residual`
- train benefit correlation: `0.983847`

| scorer | full delta | non-hard delta | hard-only delta | hard-only CI high |
|---|---:|---:|---:|---:|
| `benefit_selector` | -0.00429771 | -0.00420687 | -0.0049359 | 0.00446208 |
| `priority_residual` | -0.00429771 | -0.00420687 | -0.0049359 | 0.00445131 |
| `raw_geometry_option` | -0.00373002 | -0.00348872 | -0.00542522 | 0.00456512 |

## Verdict

Residual-benefit selector does not improve the hard-only allocation boundary over raw geometry-option scores.
