# Compute-Value Structured Ablation

- device: `cuda`
- seed: `41`
- epochs: `420`

| row | eval allocation delta | score/error rho |
|---|---:|---:|
| `full` | -0.00603784442 [-0.0108018971, -0.00129611825] | 0.889883842 |
| `state_only` | 0.0275571815 [0.0143609791, 0.0433283765] | 0.147227633 |
| `depth_only` | 0 [0, 0] | 0.862970885 |
| `ridge_full` | 0 [0, 0] | 0.283140746 |
| `refined_mv_dp` | 0.00181502343 [-0.00269426107, 0.00630281583] | 0.437380035 |
| `policy_score_balanced` | -0.00330486256 [-0.00670925986, 1.29210967e-05] | 0.396377508 |
| `exact_budget_oracle` | -0.0241221379 [-0.0305394259, -0.0192559729] | 1 |
