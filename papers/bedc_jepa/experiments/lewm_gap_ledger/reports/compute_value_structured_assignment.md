# Compute-Value Structured Assignment

- selected model: `option_conditioned_exact_budget`
- device: `cuda`
- eval anchors: `634` across `55` episodes

| policy | allocation delta | score/error rho |
|---|---:|---:|
| `exact_budget_oracle` | -0.0241221379 [-0.0304496829, -0.0194365706] | 1 |
| `learned_structured` | -0.00603784442 [-0.0104503441, -0.00168327189] | 0.889883842 |
| `ridge_structured` | 0 [0, 0] | 0.283140746 |
| `refined_mv_dp` | 0.00181502343 [-0.00279312505, 0.00629298184] | 0.437380035 |
| `policy_score_balanced` | -0.00330486256 [-0.00697205352, 0.000236732012] | 0.396377508 |
| `per_step_oracle` | -0.0305923936 [-0.0385456064, -0.0247287511] | 1 |
