# Ledger-gated rollout

- latent: `tworooms_latent_large.npz`; model: `quentinll/lewm-tworooms`
- h=1 anchor max abs delta vs `prediction_mse`: `1.6689301e-06`
- conclusion: **negative_or_inconclusive** - ledger-guided allocation did not establish a paired CI entirely below zero

| allocation | anchors | emitted steps | mean h | per emitted-step MSE | episode total error mean |
|---|---:|---:|---:|---:|---:|
| `uniform` | 634 | 1902 | 3.000000 | 0.096503421 | 3.337263763 |
| `ledger` | 634 | 1902 | 3.000000 | 0.109345142 | 3.781353822 |
| `oracle` | 634 | 1902 | 3.000000 | 0.080635862 | 2.788534727 |

## Paired Delta

- delta = ledger - uniform per emitted-step MSE: `0.012841721`
- episode bootstrap 95% CI, 500 resamples, seed 314159: `[0.005101361, 0.020897734]`

## Oracle Ceiling

- oracle per emitted-step MSE: `0.080635862`
- oracle - uniform per emitted-step MSE: `-0.015867559`

## Not Claimed

- This reports prediction budget allocation only.
- It does not claim planning or control benefit.
- It uses one checkpoint and one latent export.
