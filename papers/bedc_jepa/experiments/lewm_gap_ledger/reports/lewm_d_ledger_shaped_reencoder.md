# LeWM D: Ledger-Shaped Re-Encoder

- verdict: `D_negative_bound`
- rule: positive iff h1 q75 B-A CI95_low > 0, observed >= 0.03, C_perm not positive, h5 q75 B-A CI95_low > -0.02, and B one-step latent MSE <= 1.10*A
- device: `NVIDIA GeForce RTX 4060 Laptop GPU`; torch `2.6.0+cu124`; cuda `12.4`

## Frozen Probe AUROC

| arm | h1 q75 | h5 q75 |
|---|---:|---:|
| `A_pred_only` | 0.6046 | 0.6042 |
| `B_ledger_shaped` | 0.6084 | 0.6179 |
| `C_perm_ledger` | 0.5983 | 0.6154 |

## Paired Episode Bootstrap Delta

- h1 q75 B-A: observed `0.0038`, CI95 `[-0.0115, 0.0187]`
- h5 q75 B-A guard: observed `0.0137`, CI95 `[-0.0156, 0.0380]`
- h1 q75 C-A control: observed `-0.0063`, CI95 `[-0.0163, 0.0028]`

## Guards

- h5 B-A CI low > -0.02: `True`
- B eval one-step latent MSE <= 1.10*A: `True`
- C_perm not positive: `True`

## Not Claimed

This is not a theorem about all models or all re-encoders; it only closes boundary D for tworooms_latent_large.npz + g2n_labels_clean.npz under the declared 8GB-budget architecture, seeds, split, checkpoint rule, and frozen linear-probe evaluation.
