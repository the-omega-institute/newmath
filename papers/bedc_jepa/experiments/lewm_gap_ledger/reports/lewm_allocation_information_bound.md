# Allocation Information Bound

- status: `ok_bound_established`
- bound decision: `bound_established`
- rho*_obs 5th percentile: `0.500488`
- strongest cross-fit reader: `pairwise_RankNet` with Spearman `0.407334` [`0.319812`, `0.492946`]
- rho_max_MI CI95_high: `0.000000`

## Step 1 - Oracle-Blend Thresholds

- noise seeds: `150`
- blend grid: `0..1 step 0.02`
- rho*_obs distribution: p05 `0.500488`, median `0.573417`, p95 `0.675912`
- rho*_ci finite count: `150` (missing `0`)

## Step 2 - Cross-Fit Readers

| reader | Spearman | 95% CI | delta vs uniform | delta 95% CI | wins uniform? |
|---|---:|---:|---:|---:|:--:|
| `Ridge` | 0.349032 | [0.246401, 0.444362] | 0.012498210 | [0.001600888, 0.025588946] | no |
| `ElasticNet` | 0.355019 | [0.255933, 0.451973] | 0.008641172 | [0.001109099, 0.016917414] | no |
| `RandomForest_shallow` | 0.304852 | [0.216392, 0.396877] | 0.015965960 | [0.005151598, 0.028532218] | no |
| `ExtraTrees` | 0.312542 | [0.215231, 0.412003] | 0.015441736 | [0.003610827, 0.030230990] | no |
| `HistGradientBoosting` | 0.402662 | [0.305920, 0.498521] | 0.010907431 | [-0.000186308, 0.024492954] | no |
| `small_MLP` | 0.293220 | [0.208548, 0.373919] | 0.010101350 | [0.004247990, 0.017022411] | no |
| `pairwise_RankNet` | 0.407334 | [0.319812, 0.492946] | 0.012140223 | [-0.000162021, 0.026731045] | no |

## Step 3 - MI / Ordinal Sanity

| bucket | best classifier | MI hat nats | 95% CI | empirical rho_max CI95_high |
|---|---|---:|---:|---:|
| `3_buckets` | `RandomForest` | 0.035600 | [0.017316, 0.053402] | 0.000000 |
| `5_buckets` | `RandomForest` | 0.011048 | [-0.019725, 0.038395] | 0.000000 |

## Sanity Controls

- permutation max abs Spearman: `0.040782` (pass `True`)
- oracle Spearman: `1.000000` [`1.000000`, `1.000000`] (pass `True`)

## Bound Decision

- strongest cross-fit reader Spearman CI95_high below rho*_obs p05: `True` - pairwise_RankNet CI95_high=0.492946 vs rho*_obs_p05=0.500488
- all reader allocation delta CI95_high >= 0: `True` - no cross-fit reader beats uniform allocation by the paired episode bootstrap
- rho_max_MI CI95_high below rho*_obs p05: `True` - rho_max_MI_CI95_high=0.000000 vs rho*_obs_p05=0.500488

## Not Claimed

- not a theorem that the world model contains no allocation information
- not a claim about all possible models or all possible feature families
- not a claim beyond the current latent export, finite CPU-readable feature family, and fixed 5/1/3 allocation rule
- MI/ordinal bound is an empirical information bound, not a mathematical theorem
- single tworooms checkpoint/export and eval split only
