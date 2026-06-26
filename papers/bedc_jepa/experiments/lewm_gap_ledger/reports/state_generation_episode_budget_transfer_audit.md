# State-Generation Episode Budget-Transfer Audit

| scorer | budget | hard observed | hard CI high | hard positive episode fraction | non-hard observed |
|---|---:|---:|---:|---:|---:|
| `benefit_selector` | `budget_2` | -0.000352168 | 0 | 0 | -0.00132186 |
| `benefit_selector` | `budget_3` | -0.00522739 | 0.00363907 | 0.428571 | -0.00422762 |
| `benefit_selector` | `budget_4` | 0.00376791 | 0.021943 | 0.571429 | -0.00538738 |
| `priority_residual` | `budget_2` | -0.000352168 | 0 | 0 | -0.00132186 |
| `priority_residual` | `budget_3` | -0.00522739 | 0.00333665 | 0.428571 | -0.00422762 |
| `priority_residual` | `budget_4` | 0.00376791 | 0.0216248 | 0.571429 | -0.00538738 |
| `raw_geometry_option` | `budget_2` | -0.000418248 | 0 | 0 | -0.000559821 |
| `raw_geometry_option` | `budget_3` | -0.00555924 | 0.0036931 | 0.428571 | -0.00407201 |
| `raw_geometry_option` | `budget_4` | 0.00909481 | 0.0243355 | 0.714286 | -0.00445223 |

## Verdict

Priority-residual score does not improve the hard budget-3 episode mean over raw scores under this episode-level audit.
