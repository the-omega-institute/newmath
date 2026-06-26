# Compute-Value Policy

- device: `cuda`
- selected policy: `episode_balanced_policy`
- train anchors: `2043`
- eval anchors: `634` across `55` episodes

| policy | allocation delta | MV Spearman |
|---|---:|---:|
| `oracle` | -0.0129028727 [-0.0192216225, -0.00830111501] | 1 |
| `learned_policy` | 0.00675260285 [0.00178912359, 0.0114630014] | 0.341322143 |
| `scalar_ranknet` | 0.00821801668 [0.000645493671, 0.0165592453] | 0.449880884 |
| `inverted_oracle` | 0.0588619591 [0.0454612959, 0.0760530661] | -1 |
| `random_reference` | 0.0209383684 [0.0121102669, 0.032065757] | 0.029279444 |

The learned policy is trained on train episodes and selected on calibration episodes under the same balanced depth gate used for eval.
Eval option errors are used only after the policy scores are written.
