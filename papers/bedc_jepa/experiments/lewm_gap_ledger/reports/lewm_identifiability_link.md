# LeWM tworooms identifiability-failure link

- scientific question: 世界模型在其 latent 局部无法线性恢复环境状态的地方失败
- conclusion: **negative_or_inconclusive**
- positive criterion: positive iff any residual AUROC ci95_low > 0.5
- criterion passed by: none
- latent: `tworooms_latent_large.npz`; rows: 4991; episodes: 278
- fixed seeds: numpy=20260611, split=1701, bootstrap=314159
- failure truth: `mse > train p75`; tau=0.076702110469; eval failure rate=0.231328
- context only, not recomputed: full gap head AUROC 0.731

## Split

| split | episodes | rows | failure rate |
|---|---:|---:|---:|
| train | 167 | 3045 | 0.249918 |
| calibration | 56 | 982 | 0.233198 |
| eval | 55 | 964 | 0.231328 |

## Residual Link Tests

| residual | AUROC(y, residual) | Spearman(residual, mse) | mean residual | median residual |
|---|---:|---:|---:|---:|
| global linear | 0.4552 [0.4072, 0.5031] | -0.0515 [-0.1214, 0.0217] | 1610.702380 | 1277.142993 |
| local k=20 mean | 0.4661 [0.4177, 0.5146] | -0.0262 [-0.1038, 0.0500] | 1567.501593 | 1277.282213 |

## Protocol

- rows: `_phase1c_gap_ledger.flatten_transition_rows` using `emb`, `mse`, `pos_agent`, `pos_target`, `episode`, `t`.
- split: `_lat_lewm_port.split_episodes`, SPLIT_SEED 1701, 60/20/20.
- state vector: `concat(pos_agent, pos_target)` with 4 dimensions.
- global residual: least-squares `emb(192) -> state(4)` on train split, including intercept.
- local residual: eval rows predicted from the mean state of k=20 nearest train embeddings.
- CI: eval episode bootstrap, 500 resamples, BOOTSTRAP_SEED 314159.

## Not Claimed

- 不声称因果关系。
- 不声称全局可辨识性定理被检验。
- 仅为 tworooms 单导出上的操作化关联检验。
- 不声称结果可外推到其他环境、checkpoint、world seeds 或数据导出。
- 不重算完整 gap head；AUROC 0.731 仅作对照语境引用。

