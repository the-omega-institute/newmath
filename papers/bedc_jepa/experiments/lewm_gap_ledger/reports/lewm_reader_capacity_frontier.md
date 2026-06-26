# LeWM Reader Capacity Frontier

Pure-discriminator readers over flattened `(emb, action)` windows. OOD-aware arms train on clean train windows plus all 20 perturbed train slices.

- tau: 0.076702110469 (clean train p75 prediction_mse)
- input dim: 1212 = 6 x 202
- Delta clean monotonic non-decreasing: False

## 4x2 Frontier Table

| reader | arm | train rows | train fail rate | clean eval AUROC | bg_tint@0.6 AUROC | final color_shift | final occlusion | final brightness | final gaussian_noise |
| --- | --- | ---: | ---: | --- | --- | --- | --- | --- | --- |
| `linear` | `clean_trained` | 3045 | 0.250 | 0.693 [0.661, 0.727] | 0.660 [0.626, 0.695] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] |
| `linear` | `ood_aware` | 63945 | 0.793 | 0.617 [0.568, 0.668] | 0.673 [0.636, 0.712] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] |
| `mlp1` | `clean_trained` | 3045 | 0.250 | 0.682 [0.649, 0.716] | 0.652 [0.613, 0.687] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] |
| `mlp1` | `ood_aware` | 63945 | 0.793 | 0.594 [0.554, 0.634] | 0.676 [0.641, 0.714] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] |
| `mlp2` | `clean_trained` | 3045 | 0.250 | 0.678 [0.643, 0.709] | 0.646 [0.602, 0.686] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] |
| `mlp2` | `ood_aware` | 63945 | 0.793 | 0.593 [0.549, 0.637] | 0.671 [0.636, 0.705] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] |
| `tfm` | `clean_trained` | 3045 | 0.250 | 0.671 [0.634, 0.709] | 0.653 [0.612, 0.691] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] |
| `tfm` | `ood_aware` | 63945 | 0.793 | 0.624 [0.585, 0.666] | 0.711 [0.672, 0.751] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] | 0.500 [0.500, 0.500] |

## Delta Clean Frontier

| reader | Delta clean | ood-aware bg_tint@0.6 AUROC |
| --- | ---: | --- |
| `linear` | -0.0763 | 0.673 [0.636, 0.712] |
| `mlp1` | -0.0881 | 0.676 [0.641, 0.714] |
| `mlp2` | -0.0844 | 0.671 [0.636, 0.705] |
| `tfm` | -0.0473 | 0.711 [0.672, 0.751] |

## Conclusion

capacity frontier is not monotonic over this grid.

## not_claimed

- architecture optimality
- claims beyond this four-reader capacity grid
- claims beyond the tworooms checkpoint or this perturbation grid
