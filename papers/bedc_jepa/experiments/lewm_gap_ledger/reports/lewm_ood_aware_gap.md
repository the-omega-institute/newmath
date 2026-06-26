# Phase 2c: OOD-aware gap training

- latent: `tworooms_latent_large.npz`; H5: `_tworoom_prefix_large.h5`
- feature variant: `B_denoised_agent_room_only`
- failure truth: `prediction_mse > 0.076702` (clean train p75, fixed for clean and perturbed frames)
- bootstrap: 300 resamples, eval episodes as unit
- conclusion: **negative_or_inconclusive** - ood_aware 未能在强扰动族最终强度上建立严格的 AUROC>0.5 且 UER<vanilla 命题

## Main contrast: final strength

| family | arm | final strength | AUROC CI | vanilla UER CI | BEDC UER CI | declared gap | claim |
|---|---|---:|---:|---:|---:|---:|---|
| `color_shift` | `clean_only` | 0.4 | 0.5000 [0.5000, 0.5000] | 1.0000 [1.0000, 1.0000] | 1.0000 [1.0000, 1.0000] | 0.0000 | negative_or_inconclusive |
| `color_shift` | `ood_aware` | 0.4 | 0.5000 [0.5000, 0.5000] | 1.0000 [1.0000, 1.0000] | 0.0000 [0.0000, 0.0000] | 1.0000 | negative_or_inconclusive |
| `occlusion` | `clean_only` | 0.36 | 0.5000 [0.5000, 0.5000] | 1.0000 [1.0000, 1.0000] | 0.8900 [0.8697, 0.9102] | 0.1100 | negative_or_inconclusive |
| `occlusion` | `ood_aware` | 0.36 | 0.5000 [0.5000, 0.5000] | 1.0000 [1.0000, 1.0000] | 0.0031 [0.0000, 0.0094] | 0.9969 | negative_or_inconclusive |
| `brightness` | `clean_only` | 0.4 | 0.5000 [0.5000, 0.5000] | 1.0000 [1.0000, 1.0000] | 0.9398 [0.9212, 0.9569] | 0.0602 | negative_or_inconclusive |
| `brightness` | `ood_aware` | 0.4 | 0.5000 [0.5000, 0.5000] | 1.0000 [1.0000, 1.0000] | 0.0124 [0.0067, 0.0191] | 0.9876 | negative_or_inconclusive |
| `background_tint` | `clean_only` | 0.6 | 0.7187 [0.6852, 0.7539] | 0.3268 [0.2928, 0.3555] | 0.2552 [0.2221, 0.2938] | 0.1079 | negative_or_inconclusive |
| `background_tint` | `ood_aware` | 0.6 | 0.6866 [0.6485, 0.7194] | 0.3268 [0.2932, 0.3607] | 0.0654 [0.0513, 0.0831] | 0.6898 | positive |
| `gaussian_noise` | `clean_only` | 25 | 0.5000 [0.5000, 0.5000] | 1.0000 [1.0000, 1.0000] | 0.8714 [0.8484, 0.8941] | 0.1286 | negative_or_inconclusive |
| `gaussian_noise` | `ood_aware` | 25 | 0.5000 [0.5000, 0.5000] | 1.0000 [1.0000, 1.0000] | 0.0000 [0.0000, 0.0000] | 1.0000 | negative_or_inconclusive |

## Main contrast: nonzero pooled

| family | arm | AUROC CI | vanilla UER CI | BEDC UER CI | declared gap | claim |
|---|---|---:|---:|---:|---:|---|
| `color_shift` | `clean_only` | 0.5000 [0.5000, 0.5000] | 1.0000 [1.0000, 1.0000] | 0.9476 [0.9363, 0.9579] | 0.0524 | negative_or_inconclusive |
| `color_shift` | `ood_aware` | 0.5000 [0.5000, 0.5000] | 1.0000 [1.0000, 1.0000] | 0.0000 [0.0000, 0.0000] | 1.0000 | negative_or_inconclusive |
| `occlusion` | `clean_only` | 0.6818 [0.6608, 0.7076] | 0.8600 [0.8490, 0.8723] | 0.7484 [0.7278, 0.7685] | 0.1154 | positive |
| `occlusion` | `ood_aware` | 0.8443 [0.8270, 0.8601] | 0.8600 [0.8470, 0.8720] | 0.0545 [0.0435, 0.0649] | 0.8973 | positive |
| `brightness` | `clean_only` | 0.5612 [0.4862, 0.6343] | 0.9818 [0.9765, 0.9866] | 0.9256 [0.9071, 0.9422] | 0.0568 | negative_or_inconclusive |
| `brightness` | `ood_aware` | 0.7421 [0.7025, 0.7854] | 0.9818 [0.9762, 0.9859] | 0.0511 [0.0395, 0.0634] | 0.9455 | positive |
| `background_tint` | `clean_only` | 0.7038 [0.6690, 0.7348] | 0.3237 [0.2917, 0.3578] | 0.2510 [0.2107, 0.2874] | 0.1097 | positive |
| `background_tint` | `ood_aware` | 0.6791 [0.6431, 0.7208] | 0.3237 [0.2921, 0.3566] | 0.0654 [0.0505, 0.0807] | 0.6898 | positive |
| `gaussian_noise` | `clean_only` | 0.6589 [0.6320, 0.6856] | 0.9204 [0.9119, 0.9286] | 0.8008 [0.7797, 0.8210] | 0.1227 | positive |
| `gaussian_noise` | `ood_aware` | 0.8086 [0.7881, 0.8280] | 0.9204 [0.9118, 0.9281] | 0.0485 [0.0405, 0.0564] | 0.9326 | positive |

## Leave-one-perturbation-out

| held-out family | AUROC CI | vanilla UER CI | BEDC UER CI | declared gap | claim |
|---|---:|---:|---:|---:|---|
| `color_shift` | 0.5000 [0.5000, 0.5000] | 1.0000 [1.0000, 1.0000] | 0.0117 [0.0078, 0.0167] | 0.9883 | negative_or_inconclusive |
| `occlusion` | 0.7247 [0.7039, 0.7506] | 0.8600 [0.8462, 0.8711] | 0.1898 [0.1652, 0.2148] | 0.7396 | positive |
| `brightness` | 0.6657 [0.6208, 0.7227] | 0.9818 [0.9771, 0.9864] | 0.3631 [0.3294, 0.3977] | 0.6253 | positive |
| `background_tint` | 0.6728 [0.6373, 0.7084] | 0.3237 [0.2956, 0.3570] | 0.0176 [0.0109, 0.0257] | 0.9284 | positive |
| `gaussian_noise` | 0.6342 [0.6122, 0.6616] | 0.9204 [0.9123, 0.9276] | 0.2754 [0.2541, 0.2951] | 0.6846 | positive |

## Debt

- coverage_debt / statistical_design: single LeWM tworooms latent export with 278 episodes/4991 transitions; episode bootstrap does not replace independent world seeds
- source_debt / distinction_probe:near_target: eval accuracy 0.5902 below 0.60 separability sanity threshold
- coverage_debt / statistical_design: Phase 2c 仍只使用一个 LeWM tworooms latent export；episode bootstrap 不能替代独立 world seeds。
- metric_debt / single_class_ood_slices: 当强扰动在固定 clean p75 阈值下让 eval transition 全部失败时，AUROC 不可识别；实现报告 0.5 并标记 single_class_truth fail-closed。
- source_debt / background_tint_mask: background_tint 复用 Phase 2a 的 RGB edge/color 启发式前景 mask，不是 simulator segmentation。
