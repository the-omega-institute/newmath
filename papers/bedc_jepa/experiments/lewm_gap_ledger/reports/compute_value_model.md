# Compute-Value Model

- selected model: `ranknet_scalar`
- device: `cuda`
- eval allocation delta: `0.00821801668` `[0.0005890073, 0.0167148867]`
- eval MV Spearman: `0.449880884`

| model | calibration delta | calibration rho |
|---|---:|---:|
| `mlp` | 0.0109512337 [0.00316688849, 0.0203564604] | 0.25117857 |
| `ranknet_scalar` | 0.00482290945 [-0.00306045069, 0.0148627011] | 0.468109163 |
| `ridge_alpha_1` | 0.0119991138 [0.00757616003, 0.016753532] | 0.0875497194 |
| `ridge_alpha_10` | 0.0126947659 [0.00790061834, 0.017566609] | 0.117743941 |
| `ridge_alpha_100` | 0.0139765049 [0.00668836221, 0.0233994361] | 0.150511446 |

The selected prediction artifact contains model outputs in `predicted_mv`; eval option errors are used only by the final gate.
