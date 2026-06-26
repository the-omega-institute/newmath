# LeWM conformal-style selective guarantee

This report replaces the bare 0.5 declared-OK rule with monitor-specific thresholds calibrated on the clean calibration split.

Declared-OK is `gap_score <= tau_alpha`. The threshold is the largest calibration score whose conservative empirical failure ratio `(1 + failures_OK) / (1 + OK)` is at most alpha.

## Anchors

| anchor | observed | committed | diff |
|---|---:|---:|---:|
| logistic_clean_only.clean_eval.auroc | 0.731365322586 | 0.731365322586 | 0 |
| logistic_ood_aware.clean_eval.auroc | 0.602179820023 | 0.602179820023 | 0 |
| lat_clean.clean_eval.auroc | 0.674576230158 | 0.674576230158 | 0 |
| lat_ood_aware.clean_eval.auroc | 0.720799065619 | 0.720799065619 | 0 |

## Representative alpha=0.10 slices

| monitor | slice | risk | OK rate | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|
| logistic_clean_only | clean | 0.103 | 0.364 | [0.075, 0.139] | False |
| logistic_clean_only | background_tint:0p15 | 0.189 | 0.357 | [0.151, 0.234] | True |
| logistic_clean_only | color_shift:0p1 | 1.000 | 0.308 | [0.987, 1.000] | True |
| logistic_ood_aware | clean | 0.176 | 0.088 | [0.110, 0.271] | True |
| logistic_ood_aware | background_tint:0p15 | 0.229 | 0.086 | [0.152, 0.330] | True |
| logistic_ood_aware | color_shift:0p1 | NA | 0.000 | NA | False |
| lat_clean | clean | 0.117 | 0.195 | [0.079, 0.171] | False |
| lat_clean | background_tint:0p15 | 0.186 | 0.195 | [0.137, 0.248] | True |
| lat_clean | color_shift:0p1 | 1.000 | 0.141 | [0.973, 1.000] | True |
| lat_ood_aware | clean | 0.115 | 0.422 | [0.088, 0.150] | False |
| lat_ood_aware | background_tint:0p15 | 0.153 | 0.406 | [0.121, 0.193] | True |
| lat_ood_aware | color_shift:0p1 | NA | 0.000 | NA | False |

## Full matrix

### logistic_clean_only

- alpha=0.05: threshold=NA; calibration_status=fail_closed; covered=0

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.000 | NA | NA | False |
| color_shift:0p1 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p2 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p12 | 964 | 0.505 | 0.000 | NA | NA | False |
| occlusion:0p2 | 964 | 0.935 | 0.000 | NA | NA | False |
| occlusion:0p28 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p36 | 964 | 1.000 | 0.000 | NA | NA | False |
| brightness:0p1 | 964 | 0.930 | 0.000 | NA | NA | False |
| brightness:0p2 | 964 | 0.998 | 0.000 | NA | NA | False |
| brightness:0p3 | 964 | 0.999 | 0.000 | NA | NA | False |
| brightness:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| background_tint:0p15 | 964 | 0.317 | 0.000 | NA | NA | False |
| background_tint:0p3 | 964 | 0.324 | 0.000 | NA | NA | False |
| background_tint:0p45 | 964 | 0.327 | 0.000 | NA | NA | False |
| background_tint:0p6 | 964 | 0.327 | 0.000 | NA | NA | False |
| gaussian_noise:5 | 964 | 0.691 | 0.000 | NA | NA | False |
| gaussian_noise:10 | 964 | 0.991 | 0.000 | NA | NA | False |
| gaussian_noise:15 | 964 | 1.000 | 0.000 | NA | NA | False |
| gaussian_noise:25 | 964 | 1.000 | 0.000 | NA | NA | False |

- alpha=0.10: threshold=0.161651; calibration_status=ok; covered=382

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.364 | 0.103 | [0.075, 0.139] | False |
| color_shift:0p1 | 964 | 1.000 | 0.308 | 1.000 | [0.987, 1.000] | True |
| color_shift:0p2 | 964 | 1.000 | 0.367 | 1.000 | [0.989, 1.000] | True |
| color_shift:0p3 | 964 | 1.000 | 0.918 | 1.000 | [0.996, 1.000] | True |
| color_shift:0p4 | 964 | 1.000 | 0.983 | 1.000 | [0.996, 1.000] | True |
| occlusion:0p12 | 964 | 0.505 | 0.386 | 0.366 | [0.318, 0.416] | True |
| occlusion:0p2 | 964 | 0.935 | 0.395 | 0.919 | [0.887, 0.942] | True |
| occlusion:0p28 | 964 | 1.000 | 0.200 | 1.000 | [0.980, 1.000] | True |
| occlusion:0p36 | 964 | 1.000 | 0.239 | 1.000 | [0.984, 1.000] | True |
| brightness:0p1 | 964 | 0.930 | 0.412 | 0.909 | [0.877, 0.934] | True |
| brightness:0p2 | 964 | 0.998 | 0.422 | 0.998 | [0.986, 1.000] | True |
| brightness:0p3 | 964 | 0.999 | 0.437 | 1.000 | [0.991, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.445 | 1.000 | [0.991, 1.000] | True |
| background_tint:0p15 | 964 | 0.317 | 0.357 | 0.189 | [0.151, 0.234] | True |
| background_tint:0p3 | 964 | 0.324 | 0.356 | 0.184 | [0.146, 0.228] | True |
| background_tint:0p45 | 964 | 0.327 | 0.352 | 0.174 | [0.137, 0.218] | True |
| background_tint:0p6 | 964 | 0.327 | 0.349 | 0.167 | [0.131, 0.210] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.337 | 0.594 | [0.540, 0.646] | True |
| gaussian_noise:10 | 964 | 0.991 | 0.311 | 0.980 | [0.957, 0.991] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.255 | 1.000 | [0.985, 1.000] | True |
| gaussian_noise:25 | 964 | 1.000 | 0.174 | 1.000 | [0.978, 1.000] | True |

- alpha=0.15: threshold=0.276825; calibration_status=ok; covered=647

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.661 | 0.138 | [0.114, 0.167] | False |
| color_shift:0p1 | 964 | 1.000 | 0.585 | 1.000 | [0.993, 1.000] | True |
| color_shift:0p2 | 964 | 1.000 | 0.689 | 1.000 | [0.994, 1.000] | True |
| color_shift:0p3 | 964 | 1.000 | 0.981 | 1.000 | [0.996, 1.000] | True |
| color_shift:0p4 | 964 | 1.000 | 1.000 | 1.000 | [0.996, 1.000] | True |
| occlusion:0p12 | 964 | 0.505 | 0.680 | 0.416 | [0.379, 0.454] | True |
| occlusion:0p2 | 964 | 0.935 | 0.673 | 0.923 | [0.900, 0.941] | True |
| occlusion:0p28 | 964 | 1.000 | 0.373 | 1.000 | [0.989, 1.000] | True |
| occlusion:0p36 | 964 | 1.000 | 0.527 | 1.000 | [0.992, 1.000] | True |
| brightness:0p1 | 964 | 0.930 | 0.730 | 0.923 | [0.901, 0.941] | True |
| brightness:0p2 | 964 | 0.998 | 0.727 | 0.999 | [0.992, 1.000] | True |
| brightness:0p3 | 964 | 0.999 | 0.726 | 0.999 | [0.992, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.720 | 1.000 | [0.994, 1.000] | True |
| background_tint:0p15 | 964 | 0.317 | 0.660 | 0.222 | [0.191, 0.256] | True |
| background_tint:0p3 | 964 | 0.324 | 0.657 | 0.218 | [0.188, 0.252] | True |
| background_tint:0p45 | 964 | 0.327 | 0.654 | 0.214 | [0.184, 0.248] | True |
| background_tint:0p6 | 964 | 0.327 | 0.648 | 0.208 | [0.178, 0.242] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.616 | 0.621 | [0.582, 0.659] | True |
| gaussian_noise:10 | 964 | 0.991 | 0.566 | 0.989 | [0.976, 0.995] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.522 | 1.000 | [0.992, 1.000] | True |
| gaussian_noise:25 | 964 | 1.000 | 0.439 | 1.000 | [0.991, 1.000] | True |

- alpha=0.20: threshold=0.498306; calibration_status=ok; covered=899

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.891 | 0.189 | [0.164, 0.216] | False |
| color_shift:0p1 | 964 | 1.000 | 0.871 | 1.000 | [0.995, 1.000] | True |
| color_shift:0p2 | 964 | 1.000 | 0.916 | 1.000 | [0.996, 1.000] | True |
| color_shift:0p3 | 964 | 1.000 | 1.000 | 1.000 | [0.996, 1.000] | True |
| color_shift:0p4 | 964 | 1.000 | 1.000 | 1.000 | [0.996, 1.000] | True |
| occlusion:0p12 | 964 | 0.505 | 0.905 | 0.469 | [0.436, 0.502] | True |
| occlusion:0p2 | 964 | 0.935 | 0.918 | 0.930 | [0.911, 0.945] | True |
| occlusion:0p28 | 964 | 1.000 | 0.821 | 1.000 | [0.995, 1.000] | True |
| occlusion:0p36 | 964 | 1.000 | 0.888 | 1.000 | [0.996, 1.000] | True |
| brightness:0p1 | 964 | 0.930 | 0.944 | 0.930 | [0.911, 0.945] | True |
| brightness:0p2 | 964 | 0.998 | 0.947 | 0.998 | [0.992, 0.999] | True |
| brightness:0p3 | 964 | 0.999 | 0.939 | 0.999 | [0.994, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.940 | 1.000 | [0.996, 1.000] | True |
| background_tint:0p15 | 964 | 0.317 | 0.889 | 0.277 | [0.248, 0.307] | True |
| background_tint:0p3 | 964 | 0.324 | 0.890 | 0.281 | [0.252, 0.312] | True |
| background_tint:0p45 | 964 | 0.327 | 0.890 | 0.284 | [0.255, 0.315] | True |
| background_tint:0p6 | 964 | 0.327 | 0.892 | 0.286 | [0.257, 0.317] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.883 | 0.664 | [0.632, 0.695] | True |
| gaussian_noise:10 | 964 | 0.991 | 0.872 | 0.990 | [0.981, 0.995] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.878 | 1.000 | [0.995, 1.000] | True |
| gaussian_noise:25 | 964 | 1.000 | 0.870 | 1.000 | [0.995, 1.000] | True |

### logistic_ood_aware

- alpha=0.05: threshold=0.298048; calibration_status=ok; covered=62

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.059 | 0.246 | [0.152, 0.371] | True |
| color_shift:0p1 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p2 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p12 | 964 | 0.505 | 0.049 | 0.362 | [0.240, 0.505] | True |
| occlusion:0p2 | 964 | 0.935 | 0.010 | 0.900 | [0.596, 0.982] | True |
| occlusion:0p28 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p36 | 964 | 1.000 | 0.000 | NA | NA | False |
| brightness:0p1 | 964 | 0.930 | 0.020 | 0.947 | [0.754, 0.991] | True |
| brightness:0p2 | 964 | 0.998 | 0.004 | 1.000 | [0.510, 1.000] | True |
| brightness:0p3 | 964 | 0.999 | 0.004 | 1.000 | [0.510, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.001 | 1.000 | [0.207, 1.000] | True |
| background_tint:0p15 | 964 | 0.317 | 0.059 | 0.281 | [0.181, 0.408] | True |
| background_tint:0p3 | 964 | 0.324 | 0.059 | 0.281 | [0.181, 0.408] | True |
| background_tint:0p45 | 964 | 0.327 | 0.059 | 0.281 | [0.181, 0.408] | True |
| background_tint:0p6 | 964 | 0.327 | 0.059 | 0.281 | [0.181, 0.408] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.033 | 0.594 | [0.423, 0.745] | True |
| gaussian_noise:10 | 964 | 0.991 | 0.009 | 1.000 | [0.701, 1.000] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.000 | NA | NA | False |
| gaussian_noise:25 | 964 | 1.000 | 0.000 | NA | NA | False |

- alpha=0.10: threshold=0.332756; calibration_status=ok; covered=92

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.088 | 0.176 | [0.110, 0.271] | True |
| color_shift:0p1 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p2 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p12 | 964 | 0.505 | 0.070 | 0.373 | [0.267, 0.493] | True |
| occlusion:0p2 | 964 | 0.935 | 0.017 | 0.875 | [0.640, 0.965] | True |
| occlusion:0p28 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p36 | 964 | 1.000 | 0.000 | NA | NA | False |
| brightness:0p1 | 964 | 0.930 | 0.028 | 0.963 | [0.817, 0.993] | True |
| brightness:0p2 | 964 | 0.998 | 0.006 | 1.000 | [0.610, 1.000] | True |
| brightness:0p3 | 964 | 0.999 | 0.004 | 1.000 | [0.510, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.002 | 1.000 | [0.342, 1.000] | True |
| background_tint:0p15 | 964 | 0.317 | 0.086 | 0.229 | [0.152, 0.330] | True |
| background_tint:0p3 | 964 | 0.324 | 0.086 | 0.229 | [0.152, 0.330] | True |
| background_tint:0p45 | 964 | 0.327 | 0.086 | 0.229 | [0.152, 0.330] | True |
| background_tint:0p6 | 964 | 0.327 | 0.086 | 0.229 | [0.152, 0.330] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.052 | 0.620 | [0.482, 0.741] | True |
| gaussian_noise:10 | 964 | 0.991 | 0.011 | 1.000 | [0.741, 1.000] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.000 | NA | NA | False |
| gaussian_noise:25 | 964 | 1.000 | 0.000 | NA | NA | False |

- alpha=0.15: threshold=0.544685; calibration_status=ok; covered=366

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.402 | 0.160 | [0.127, 0.200] | False |
| color_shift:0p1 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p2 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p12 | 964 | 0.505 | 0.374 | 0.391 | [0.342, 0.442] | True |
| occlusion:0p2 | 964 | 0.935 | 0.165 | 0.899 | [0.843, 0.937] | True |
| occlusion:0p28 | 964 | 1.000 | 0.002 | 1.000 | [0.342, 1.000] | True |
| occlusion:0p36 | 964 | 1.000 | 0.006 | 1.000 | [0.610, 1.000] | True |
| brightness:0p1 | 964 | 0.930 | 0.186 | 0.905 | [0.853, 0.940] | True |
| brightness:0p2 | 964 | 0.998 | 0.072 | 1.000 | [0.947, 1.000] | True |
| brightness:0p3 | 964 | 0.999 | 0.033 | 1.000 | [0.893, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.018 | 1.000 | [0.816, 1.000] | True |
| background_tint:0p15 | 964 | 0.317 | 0.389 | 0.208 | [0.170, 0.252] | True |
| background_tint:0p3 | 964 | 0.324 | 0.389 | 0.203 | [0.165, 0.246] | True |
| background_tint:0p45 | 964 | 0.327 | 0.389 | 0.205 | [0.168, 0.249] | True |
| background_tint:0p6 | 964 | 0.327 | 0.389 | 0.205 | [0.168, 0.249] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.261 | 0.591 | [0.530, 0.650] | True |
| gaussian_noise:10 | 964 | 0.991 | 0.100 | 0.990 | [0.943, 0.998] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.022 | 1.000 | [0.845, 1.000] | True |
| gaussian_noise:25 | 964 | 1.000 | 0.001 | 1.000 | [0.207, 1.000] | True |

- alpha=0.20: threshold=0.765278; calibration_status=ok; covered=772

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.789 | 0.198 | [0.172, 0.228] | False |
| color_shift:0p1 | 964 | 1.000 | 0.049 | 1.000 | [0.924, 1.000] | True |
| color_shift:0p2 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p12 | 964 | 0.505 | 0.771 | 0.456 | [0.421, 0.492] | True |
| occlusion:0p2 | 964 | 0.935 | 0.503 | 0.901 | [0.871, 0.925] | True |
| occlusion:0p28 | 964 | 1.000 | 0.035 | 1.000 | [0.898, 1.000] | True |
| occlusion:0p36 | 964 | 1.000 | 0.086 | 1.000 | [0.956, 1.000] | True |
| brightness:0p1 | 964 | 0.930 | 0.602 | 0.919 | [0.894, 0.939] | True |
| brightness:0p2 | 964 | 0.998 | 0.368 | 0.997 | [0.984, 1.000] | True |
| brightness:0p3 | 964 | 0.999 | 0.227 | 1.000 | [0.983, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.124 | 1.000 | [0.969, 1.000] | True |
| background_tint:0p15 | 964 | 0.317 | 0.768 | 0.246 | [0.216, 0.278] | True |
| background_tint:0p3 | 964 | 0.324 | 0.761 | 0.238 | [0.209, 0.271] | True |
| background_tint:0p45 | 964 | 0.327 | 0.761 | 0.240 | [0.210, 0.272] | True |
| background_tint:0p6 | 964 | 0.327 | 0.761 | 0.240 | [0.210, 0.272] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.694 | 0.652 | [0.615, 0.687] | True |
| gaussian_noise:10 | 964 | 0.991 | 0.411 | 0.990 | [0.974, 0.996] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.144 | 1.000 | [0.973, 1.000] | True |
| gaussian_noise:25 | 964 | 1.000 | 0.026 | 1.000 | [0.867, 1.000] | True |

### lat_clean

- alpha=0.05: threshold=NA; calibration_status=fail_closed; covered=0

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.000 | NA | NA | False |
| color_shift:0p1 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p2 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p12 | 964 | 0.500 | 0.000 | NA | NA | False |
| occlusion:0p2 | 964 | 0.934 | 0.000 | NA | NA | False |
| occlusion:0p28 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p36 | 964 | 1.000 | 0.000 | NA | NA | False |
| brightness:0p1 | 964 | 0.930 | 0.000 | NA | NA | False |
| brightness:0p2 | 964 | 0.998 | 0.000 | NA | NA | False |
| brightness:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| brightness:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| background_tint:0p15 | 964 | 0.314 | 0.000 | NA | NA | False |
| background_tint:0p3 | 964 | 0.323 | 0.000 | NA | NA | False |
| background_tint:0p45 | 964 | 0.324 | 0.000 | NA | NA | False |
| background_tint:0p6 | 964 | 0.324 | 0.000 | NA | NA | False |
| gaussian_noise:5 | 964 | 0.691 | 0.000 | NA | NA | False |
| gaussian_noise:10 | 964 | 0.990 | 0.000 | NA | NA | False |
| gaussian_noise:15 | 964 | 1.000 | 0.000 | NA | NA | False |
| gaussian_noise:25 | 964 | 1.000 | 0.000 | NA | NA | False |

- alpha=0.10: threshold=0.000001; calibration_status=ok; covered=191

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.195 | 0.117 | [0.079, 0.171] | False |
| color_shift:0p1 | 964 | 1.000 | 0.141 | 1.000 | [0.973, 1.000] | True |
| color_shift:0p2 | 964 | 1.000 | 0.030 | 1.000 | [0.883, 1.000] | True |
| color_shift:0p3 | 964 | 1.000 | 0.002 | 1.000 | [0.342, 1.000] | True |
| color_shift:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p12 | 964 | 0.500 | 0.197 | 0.389 | [0.323, 0.460] | True |
| occlusion:0p2 | 964 | 0.934 | 0.173 | 0.886 | [0.829, 0.926] | True |
| occlusion:0p28 | 964 | 1.000 | 0.183 | 1.000 | [0.979, 1.000] | True |
| occlusion:0p36 | 964 | 1.000 | 0.199 | 1.000 | [0.980, 1.000] | True |
| brightness:0p1 | 964 | 0.930 | 0.220 | 0.863 | [0.810, 0.903] | True |
| brightness:0p2 | 964 | 0.998 | 0.217 | 1.000 | [0.982, 1.000] | True |
| brightness:0p3 | 964 | 1.000 | 0.201 | 1.000 | [0.981, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.195 | 1.000 | [0.980, 1.000] | True |
| background_tint:0p15 | 964 | 0.314 | 0.195 | 0.186 | [0.137, 0.248] | True |
| background_tint:0p3 | 964 | 0.323 | 0.198 | 0.199 | [0.149, 0.261] | True |
| background_tint:0p45 | 964 | 0.324 | 0.201 | 0.222 | [0.169, 0.285] | True |
| background_tint:0p6 | 964 | 0.324 | 0.198 | 0.220 | [0.167, 0.284] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.193 | 0.473 | [0.403, 0.545] | True |
| gaussian_noise:10 | 964 | 0.990 | 0.192 | 0.973 | [0.938, 0.988] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.144 | 1.000 | [0.973, 1.000] | True |
| gaussian_noise:25 | 964 | 1.000 | 0.059 | 1.000 | [0.937, 1.000] | True |

- alpha=0.15: threshold=0.065308; calibration_status=ok; covered=671

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.663 | 0.161 | [0.135, 0.192] | False |
| color_shift:0p1 | 964 | 1.000 | 0.655 | 1.000 | [0.994, 1.000] | True |
| color_shift:0p2 | 964 | 1.000 | 0.761 | 1.000 | [0.995, 1.000] | True |
| color_shift:0p3 | 964 | 1.000 | 0.900 | 1.000 | [0.996, 1.000] | True |
| color_shift:0p4 | 964 | 1.000 | 0.985 | 1.000 | [0.996, 1.000] | True |
| occlusion:0p12 | 964 | 0.500 | 0.667 | 0.437 | [0.399, 0.476] | True |
| occlusion:0p2 | 964 | 0.934 | 0.675 | 0.919 | [0.895, 0.937] | True |
| occlusion:0p28 | 964 | 1.000 | 0.722 | 1.000 | [0.995, 1.000] | True |
| occlusion:0p36 | 964 | 1.000 | 0.753 | 1.000 | [0.995, 1.000] | True |
| brightness:0p1 | 964 | 0.930 | 0.685 | 0.917 | [0.893, 0.935] | True |
| brightness:0p2 | 964 | 0.998 | 0.704 | 0.997 | [0.989, 0.999] | True |
| brightness:0p3 | 964 | 1.000 | 0.687 | 1.000 | [0.994, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.682 | 1.000 | [0.994, 1.000] | True |
| background_tint:0p15 | 964 | 0.314 | 0.663 | 0.238 | [0.206, 0.272] | True |
| background_tint:0p3 | 964 | 0.323 | 0.666 | 0.255 | [0.223, 0.291] | True |
| background_tint:0p45 | 964 | 0.324 | 0.668 | 0.262 | [0.230, 0.298] | True |
| background_tint:0p6 | 964 | 0.324 | 0.672 | 0.267 | [0.234, 0.302] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.648 | 0.643 | [0.605, 0.680] | True |
| gaussian_noise:10 | 964 | 0.990 | 0.630 | 0.985 | [0.972, 0.992] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.603 | 1.000 | [0.993, 1.000] | True |
| gaussian_noise:25 | 964 | 1.000 | 0.442 | 1.000 | [0.991, 1.000] | True |

- alpha=0.20: threshold=0.999751; calibration_status=ok; covered=906

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.930 | 0.212 | [0.186, 0.240] | False |
| color_shift:0p1 | 964 | 1.000 | 0.965 | 1.000 | [0.996, 1.000] | True |
| color_shift:0p2 | 964 | 1.000 | 0.999 | 1.000 | [0.996, 1.000] | True |
| color_shift:0p3 | 964 | 1.000 | 1.000 | 1.000 | [0.996, 1.000] | True |
| color_shift:0p4 | 964 | 1.000 | 1.000 | 1.000 | [0.996, 1.000] | True |
| occlusion:0p12 | 964 | 0.500 | 0.930 | 0.480 | [0.448, 0.513] | True |
| occlusion:0p2 | 964 | 0.934 | 0.946 | 0.930 | [0.911, 0.945] | True |
| occlusion:0p28 | 964 | 1.000 | 0.970 | 1.000 | [0.996, 1.000] | True |
| occlusion:0p36 | 964 | 1.000 | 0.969 | 1.000 | [0.996, 1.000] | True |
| brightness:0p1 | 964 | 0.930 | 0.945 | 0.928 | [0.909, 0.943] | True |
| brightness:0p2 | 964 | 0.998 | 0.948 | 0.998 | [0.992, 0.999] | True |
| brightness:0p3 | 964 | 1.000 | 0.949 | 1.000 | [0.996, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.947 | 1.000 | [0.996, 1.000] | True |
| background_tint:0p15 | 964 | 0.314 | 0.929 | 0.296 | [0.267, 0.326] | True |
| background_tint:0p3 | 964 | 0.323 | 0.924 | 0.304 | [0.275, 0.335] | True |
| background_tint:0p45 | 964 | 0.324 | 0.924 | 0.308 | [0.278, 0.339] | True |
| background_tint:0p6 | 964 | 0.324 | 0.924 | 0.308 | [0.278, 0.339] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.920 | 0.687 | [0.655, 0.716] | True |
| gaussian_noise:10 | 964 | 0.990 | 0.907 | 0.989 | [0.979, 0.994] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.889 | 1.000 | [0.996, 1.000] | True |
| gaussian_noise:25 | 964 | 1.000 | 0.856 | 1.000 | [0.995, 1.000] | True |

### lat_ood_aware

- alpha=0.05: threshold=NA; calibration_status=fail_closed; covered=0

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.000 | NA | NA | False |
| color_shift:0p1 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p2 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p12 | 964 | 0.500 | 0.000 | NA | NA | False |
| occlusion:0p2 | 964 | 0.934 | 0.000 | NA | NA | False |
| occlusion:0p28 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p36 | 964 | 1.000 | 0.000 | NA | NA | False |
| brightness:0p1 | 964 | 0.930 | 0.000 | NA | NA | False |
| brightness:0p2 | 964 | 0.998 | 0.000 | NA | NA | False |
| brightness:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| brightness:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| background_tint:0p15 | 964 | 0.314 | 0.000 | NA | NA | False |
| background_tint:0p3 | 964 | 0.323 | 0.000 | NA | NA | False |
| background_tint:0p45 | 964 | 0.324 | 0.000 | NA | NA | False |
| background_tint:0p6 | 964 | 0.324 | 0.000 | NA | NA | False |
| gaussian_noise:5 | 964 | 0.691 | 0.000 | NA | NA | False |
| gaussian_noise:10 | 964 | 0.990 | 0.000 | NA | NA | False |
| gaussian_noise:15 | 964 | 1.000 | 0.000 | NA | NA | False |
| gaussian_noise:25 | 964 | 1.000 | 0.000 | NA | NA | False |

- alpha=0.10: threshold=0.034479; calibration_status=ok; covered=433

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.422 | 0.115 | [0.088, 0.150] | False |
| color_shift:0p1 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p2 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p12 | 964 | 0.500 | 0.185 | 0.264 | [0.205, 0.333] | True |
| occlusion:0p2 | 964 | 0.934 | 0.010 | 0.900 | [0.596, 0.982] | True |
| occlusion:0p28 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p36 | 964 | 1.000 | 0.000 | NA | NA | False |
| brightness:0p1 | 964 | 0.930 | 0.029 | 0.893 | [0.728, 0.963] | True |
| brightness:0p2 | 964 | 0.998 | 0.004 | 1.000 | [0.510, 1.000] | True |
| brightness:0p3 | 964 | 1.000 | 0.002 | 1.000 | [0.342, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.001 | 1.000 | [0.207, 1.000] | True |
| background_tint:0p15 | 964 | 0.314 | 0.406 | 0.153 | [0.121, 0.193] | True |
| background_tint:0p3 | 964 | 0.323 | 0.410 | 0.144 | [0.113, 0.182] | True |
| background_tint:0p45 | 964 | 0.324 | 0.414 | 0.148 | [0.116, 0.186] | True |
| background_tint:0p6 | 964 | 0.324 | 0.418 | 0.149 | [0.117, 0.187] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.126 | 0.455 | [0.369, 0.543] | True |
| gaussian_noise:10 | 964 | 0.990 | 0.009 | 1.000 | [0.701, 1.000] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.000 | NA | NA | False |
| gaussian_noise:25 | 964 | 1.000 | 0.000 | NA | NA | False |

- alpha=0.15: threshold=0.697964; calibration_status=ok; covered=715

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.721 | 0.157 | [0.132, 0.186] | False |
| color_shift:0p1 | 964 | 1.000 | 0.005 | 1.000 | [0.566, 1.000] | True |
| color_shift:0p2 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p12 | 964 | 0.500 | 0.461 | 0.340 | [0.298, 0.385] | True |
| occlusion:0p2 | 964 | 0.934 | 0.054 | 0.769 | [0.639, 0.863] | True |
| occlusion:0p28 | 964 | 1.000 | 0.001 | 1.000 | [0.207, 1.000] | True |
| occlusion:0p36 | 964 | 1.000 | 0.000 | NA | NA | False |
| brightness:0p1 | 964 | 0.930 | 0.110 | 0.868 | [0.790, 0.920] | True |
| brightness:0p2 | 964 | 0.998 | 0.020 | 1.000 | [0.832, 1.000] | True |
| brightness:0p3 | 964 | 1.000 | 0.002 | 1.000 | [0.342, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.001 | 1.000 | [0.207, 1.000] | True |
| background_tint:0p15 | 964 | 0.314 | 0.688 | 0.214 | [0.185, 0.247] | True |
| background_tint:0p3 | 964 | 0.323 | 0.679 | 0.206 | [0.177, 0.239] | True |
| background_tint:0p45 | 964 | 0.324 | 0.680 | 0.203 | [0.174, 0.235] | True |
| background_tint:0p6 | 964 | 0.324 | 0.682 | 0.202 | [0.173, 0.235] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.324 | 0.590 | [0.534, 0.643] | True |
| gaussian_noise:10 | 964 | 0.990 | 0.024 | 0.913 | [0.732, 0.976] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.000 | NA | NA | False |
| gaussian_noise:25 | 964 | 1.000 | 0.000 | NA | NA | False |

- alpha=0.20: threshold=0.989465; calibration_status=ok; covered=892

| slice | n | fail rate | OK rate | risk | Wilson 95% | violated |
|---|---:|---:|---:|---:|---:|---:|
| clean | 964 | 0.231 | 0.906 | 0.196 | [0.171, 0.224] | False |
| color_shift:0p1 | 964 | 1.000 | 0.043 | 1.000 | [0.914, 1.000] | True |
| color_shift:0p2 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p3 | 964 | 1.000 | 0.000 | NA | NA | False |
| color_shift:0p4 | 964 | 1.000 | 0.000 | NA | NA | False |
| occlusion:0p12 | 964 | 0.500 | 0.774 | 0.429 | [0.394, 0.465] | True |
| occlusion:0p2 | 964 | 0.934 | 0.242 | 0.863 | [0.813, 0.901] | True |
| occlusion:0p28 | 964 | 1.000 | 0.003 | 1.000 | [0.439, 1.000] | True |
| occlusion:0p36 | 964 | 1.000 | 0.010 | 1.000 | [0.722, 1.000] | True |
| brightness:0p1 | 964 | 0.930 | 0.332 | 0.903 | [0.866, 0.931] | True |
| brightness:0p2 | 964 | 0.998 | 0.083 | 1.000 | [0.954, 1.000] | True |
| brightness:0p3 | 964 | 1.000 | 0.022 | 1.000 | [0.845, 1.000] | True |
| brightness:0p4 | 964 | 1.000 | 0.003 | 1.000 | [0.439, 1.000] | True |
| background_tint:0p15 | 964 | 0.314 | 0.890 | 0.265 | [0.236, 0.295] | True |
| background_tint:0p3 | 964 | 0.323 | 0.873 | 0.259 | [0.230, 0.290] | True |
| background_tint:0p45 | 964 | 0.324 | 0.856 | 0.245 | [0.217, 0.275] | True |
| background_tint:0p6 | 964 | 0.324 | 0.853 | 0.245 | [0.216, 0.275] | True |
| gaussian_noise:5 | 964 | 0.691 | 0.632 | 0.629 | [0.590, 0.666] | True |
| gaussian_noise:10 | 964 | 0.990 | 0.121 | 0.940 | [0.882, 0.971] | True |
| gaussian_noise:15 | 964 | 1.000 | 0.005 | 1.000 | [0.566, 1.000] | True |
| gaussian_noise:25 | 964 | 1.000 | 0.000 | NA | NA | False |

## Conclusion

Clean slice violations: 2/16 monitor-alpha cells. Background_tint violations: 52/64 cells. Non-background OOD violations: 166/256 cells; zero-OK fail-closed cells among them: 90. Interpretation: clean calibration carries the intended finite-sample selective-risk meaning only where exchangeability is plausible; OOD slices are coverage mapping, not a theorem transfer.

## Not claimed

This is selective risk control by finite-sample conservative calibration, not a full split-conformal alpha-bound theorem. Exchangeability naturally breaks under perturbation slices; that break is the object being mapped.
