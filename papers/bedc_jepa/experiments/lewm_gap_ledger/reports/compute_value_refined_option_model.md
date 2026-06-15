# Compute-Value Refined Option Model

- selected model: `mlp`
- device: `cuda`
- eval allocation delta: `0.00183734673` `[-0.00199480044, 0.00656298852]`
- oracle delta: `-0.0305923936` `[-0.0381025082, -0.024755602]`
- reused policy-score delta: `-0.00330486256` `[-0.00679135255, 0.000195963901]`
- eval score Spearman: `0.331491813`

| candidate | calibration delta | calibration rho |
|---|---:|---:|
| `mlp` | -0.00136157871 [-0.00532947322, 0.00294080734] | 0.35118882 |
| `ridge_alpha_1` | 0.00336184251 [0.000699243011, 0.0060563084] | 0.0875497194 |
| `ridge_alpha_10` | 0.00389655029 [0.00113556869, 0.00689765235] | 0.117743941 |
| `ridge_alpha_100` | 0.00241393157 [-0.00276770833, 0.00814189958] | 0.150511446 |
