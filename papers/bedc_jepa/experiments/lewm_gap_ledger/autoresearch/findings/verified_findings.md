# Verified autoresearch findings

Only findings that passed the mechanical gates (anchor / reproducibility /
criterion / overclaim / provenance) **and** an independent adversarial
verification (sound / sound-but-scoped) are listed. Artifacts and pending
findings are held back (fail-closed) and not exported.

| Hypothesis | Status | Adversarial | Metric | Value | CI | Claim |
| --- | --- | --- | --- | --- | --- | --- |
| fi-001.cvar-tail | positive | sound-but-scoped | allocation_delta | -0.01993813485867657 | [-0.03214831046980404, -0.006911886751007898] | 在 PushT latent 的固定 episode bootstrap 下，CVaR 尾部加权臂的 allocation_delta CI 严格低于 0。 |
| fi-002.pusht-independent-export | positive | sound-but-scoped | uer_delta | -0.09732016925246828 | [-0.14423327771879266, -0.06014446167934367] | A: 独立 stratified C3b 导出上 learned-vs-vanilla UER delta=-0.0973201692525 (CI [-0.144233277719,-0.0601444616793])；posthoc h1/q75 AUROC=0.74436849464。 |
| fi-003.multi-horizon-ledger-vector | fail-closed | sound | horizon_vector_auroc_gain | -0.024152542372881447 | [-0.18301184714956545, 0.1530174731182795] | tworooms latent 上已去除 target-horizon label 泄漏；多 horizon past-gap ledger 向量 vs 单 horizon 标量的配对 AUROC 增益为 -0.024153, 95% CI=[-0.183012,0.153017] (vector AUROC=0.586017, scalar AUROC=0.610169)，delta_ci_above_zero 判据结论为 unidentifiable。 |
| fi-004.cross-env-reader-transfer | fail-closed | sound-but-scoped | transfer_auroc | 0.43081627526225974 | [0.3186470115670378, 0.5454226672228201] | A reader trained on tworooms pre-anchor gap history scored reacher zero-shot transfer_auroc=0.430816275262 with 95% CI [0.318647011567,0.545422667223], so the null-0.5 CI criterion is unidentifiable. |
| fi-005.conformal-selective-risk-holds | fail-closed | sound | risk_margin | 0.007651715039577844 | [-0.001522842639593902, 0.01790969584505204] | α=0.10 下 admitted realized risk=0.0923482849604, risk_margin=0.00765171503958, CI=[-0.00152284263959,0.0179096958451]；CI 跨 0 或单类/空 admitted，不可识别并 fail-closed。 |
| fi-006.reader-capacity-saturation | fail-closed | sound | mlp_minus_linear_auroc | -0.0022693850874166976 | [-0.027704329611362644, 0.023874868976349835] | MLP AUROC=0.619821, linear AUROC=0.622090, gain=-0.002269, 95% CI=[-0.027704,0.023875]; delta_ci_above_zero=unidentifiable. |
| fi-007.native-predictor-pilot | positive | sound | native_minus_trivial_mse | -0.5866847722829981 | [-0.6256876679751641, -0.5447526989343108] | large native_mse=0.880457, trivial_mse=1.467142, lewm_mse=0.069740, ratio=12.624886; small native_mse=0.891380 ratio=12.781513, larger narrowed native-LeWM gap by 0.010923. |

