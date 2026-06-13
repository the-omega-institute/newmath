# LEWM Allocation Bridge

- status: `ok`
- positive rule: per arm positive iff paired episode-bootstrap CI for allocation minus uniform is entirely < 0
- oracle delta: `-0.015867561` [`-0.021509230`, `-0.010840608`]

## Allocation Results

| arm | delta vs uniform | 95% CI | Spearman episode mean | oracle gap | verdict |
|---|---:|---:|---:|---:|---|
| `R1` | 0.008553091 | [-0.002342385, 0.022684464] | 0.459851 | 0.024420653 | not_positive |
| `R2` | 0.005886841 | [-0.003261533, 0.018418622] | 0.507834 | 0.021754403 | not_positive |
| `R3` | 0.009941337 | [-0.001753892, 0.023754522] | 0.432186 | 0.025808898 | not_positive |

## Controls

| control | delta vs uniform | 95% CI | Spearman episode mean | oracle gap |
|---|---:|---:|---:|---:|
| `R1_permuted` | 0.016834858 | [0.008457435, 0.026806428] | 0.159798 | 0.032702419 |
| `oracle` | -0.015867561 | [-0.021509230, -0.010840608] | 1.000000 | 0.000000000 |

## R3 Anchor

- E clean h=1 AUROC: `0.738515205859875`; target `0.738515205859875`; abs delta `0`.

## Not Claimed

- single checkpoint single export
- prediction budget allocation rather than planning or control
- no hyperparameter scan
- no selection of only the best arm
