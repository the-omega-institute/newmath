# State-Generation Episode Transfer Anatomy

- rows: `['episode_best_seed', 'episode_objective', 'seed_mean', 'episode_balanced', 'episode_regret', 'episode_dual_price']`
- shared top-harm episodes: `3`

| row | harmful episodes | delta mean | delta p90 | regret mean | top-harm share |
|---|---:|---:|---:|---:|---:|
| `episode_best_seed` | 18 | -0.00451539 | 0.0230785 | 0.0202297 | 0.889609 |
| `episode_objective` | 18 | -0.00291742 | 0.0199125 | 0.0218277 | 0.88995 |
| `seed_mean` | 17 | -0.00451746 | 0.0230785 | 0.0202277 | 0.966057 |
| `episode_balanced` | 20 | -0.00171657 | 0.0250929 | 0.0230286 | 0.888628 |
| `episode_regret` | 19 | -0.000764837 | 0.0140019 | 0.0239803 | 0.895278 |
| `episode_dual_price` | 19 | -0.00248191 | 0.0230785 | 0.0222632 | 0.924865 |

## Top Harm Episodes

- `episode_best_seed`: `[115, 213, 81, 201, 145]`
- `episode_objective`: `[201, 213, 81, 193, 145]`
- `seed_mean`: `[115, 201, 145, 213, 81]`
- `episode_balanced`: `[115, 213, 145, 81, 277]`
- `episode_regret`: `[115, 213, 145, 81, 193]`
- `episode_dual_price`: `[115, 213, 81, 201, 145]`
