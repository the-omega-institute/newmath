# G2N Native Ledger

- status: `ok`
- Outcome 1: **not_improved**
- Outcome 2: **negative_or_inconclusive**
- lambda: fail=1.0, teacher=0.5, unlogged=0.5, budget=0.5

## Clean Eval AUROC/UER

| arm | h=1 AUROC | h=1 UER | h=5 AUROC | h=5 UER |
|---|---:|---:|---:|---:|
| `D` | 0.660840 [0.617750, 0.714379] | 0.151054 [0.123723, 0.180623] | 0.406499 [0.351450, 0.462797] | 0.148265 [0.115110, 0.184380] |
| `E` | 0.738515 [0.696238, 0.781118] | 0.129977 [0.108139, 0.154707] | 0.710160 [0.657333, 0.760760] | 0.151420 [0.117498, 0.192031] |
| `F` | 0.691660 [0.654755, 0.732654] | 0.175644 [0.152122, 0.205685] | 0.635691 [0.566033, 0.694659] | 0.159306 [0.122023, 0.202562] |
| `G` | 0.501411 [0.456173, 0.545298] | 0.000000 [0.000000, 0.000000] | 0.486064 [0.430371, 0.546416] | 0.264984 [0.215898, 0.316168] |
| `H` | 0.455941 [0.412243, 0.511133] | 0.000000 [0.000000, 0.000000] | 0.503436 [0.440196, 0.574331] | 0.264984 [0.215898, 0.316168] |

## Budget Delta

| allocation score | delta observed | 95% CI | verdict |
|---|---:|---:|---|
| `F` | 0.011063582 | [0.000956363, 0.023222601] | not_positive |
| `G` | 0.028862423 | [0.018784740, 0.040570684] | not_positive |
| `H` | 0.017723470 | [0.008250257, 0.028187468] | not_positive |
| `oracle` | -0.015867561 | [-0.021509230, -0.010840608] | positive |

## Outcome Rules

- Outcome 1 improved iff F clean eval h=1 AUROC observed >= 0.721.
- Outcome 1 robust-win-kept iff F clean eval h=1 AUROC CI separates from B=0.602.
- Outcome 2 positive iff F budget delta CI is entirely below 0.

## Not Claimed

- single checkpoint, single export
- lambda values were not tuned or scanned
- no planning or control benefit is claimed; budget allocation is prediction budget only
- perturb eval future-token cache is absent, so perturb eval uses masked zero future tokens
