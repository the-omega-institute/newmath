# Compute-Value Joint Horizon Option

- device: `cuda`
- selected row: `option_only`
- eval anchors: `634` across `55` episodes

| row | allocation delta | score/error rho | mean horizon AUROC |
|---|---:|---:|---:|
| `exact_budget_oracle` | -0.0241221379 [-0.0304496829, -0.0194365706] | 1 | 0 |
| `option_only` | 0.000166461109 [-0.000138248186, 0.000498942464] | 0.837135116 | 0.532713878 |
| `joint_horizon_option` | 0.00465786412 [2.97330543e-07, 0.0112797598] | 0.873741152 | 0.751730402 |
| `horizon_risk_dp` | 0.00702512024 [0.00227370873, 0.0119218703] | 0.0322853293 | 0 |
