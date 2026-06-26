# Cross-Env Native Horizon Ledger

- status: ok
- no OOD arm claimed: three-environment pipeline has no perturbation/OOD evaluation path in this protocol
- seeds: numpy=20260611, torch=20260611, split=1701, bootstrap=314159
- arm: E only; epochs=30, batch=256, lr=0.001, d_model=64

| env | h=1 AUROC | h=3 AUROC | h=5 AUROC | h=10 AUROC | h=1 probe AUROC | conclusion |
|---|---:|---:|---:|---:|---:|---|
| reacher | 0.734 [0.698, 0.772] | 0.725 [0.677, 0.768] | 0.701 [0.636, 0.759] | 0.696 [0.634, 0.758] | 0.662 [0.619, 0.701] | native horizon ledger was detectable for all preregistered horizons at q=75 |
| cube | 0.602 [0.562, 0.641] | 0.672 [0.616, 0.728] | 0.667 [0.618, 0.720] | 0.631 [0.556, 0.689] | 0.610 [0.568, 0.652] | native horizon ledger was detectable for all preregistered horizons at q=75 |
| pusht | 1.000 [1.000, 1.000] | 0.999 [0.997, 1.000] | 1.000 [1.000, 1.000] | 1.000 [1.000, 1.000] | 1.000 [1.000, 1.000] | native horizon ledger was detectable for all preregistered horizons at q=75 |

## reacher

- label file: `reports/crossenv_horizon_labels_reacher.npz`
- h=1 anchor max |delta|: `1.96011977e-08`
- train/eval anchors: `3420` / `1140`

| h | tau q50 | tau q75 | tau q90 | eval base rate q75 | detectable |
|---:|---:|---:|---:|---:|---|
| 1 | 0.0056814236 | 0.0076381917 | 0.010328385 | 0.264 | true |
| 3 | 0.01141033 | 0.016732904 | 0.023723235 | 0.263 | true |
| 5 | 0.015720272 | 0.024463729 | 0.035793528 | 0.237 | true |
| 10 | 0.02681389 | 0.04441902 | 0.069495321 | 0.257 | true |

## cube

- label file: `reports/crossenv_horizon_labels_cube.npz`
- h=1 anchor max |delta|: `1.42296723e-08`
- train/eval anchors: `3420` / `1140`

| h | tau q50 | tau q75 | tau q90 | eval base rate q75 | detectable |
|---:|---:|---:|---:|---:|---|
| 1 | 0.0033808655 | 0.004918139 | 0.0074454699 | 0.249 | true |
| 3 | 0.0092821188 | 0.016106574 | 0.029726672 | 0.247 | true |
| 5 | 0.015897804 | 0.031436956 | 0.060740925 | 0.232 | true |
| 10 | 0.035212615 | 0.064611529 | 0.12832992 | 0.270 | true |

## pusht

- label file: `reports/crossenv_horizon_labels_pusht.npz`
- h=1 anchor max |delta|: `2.67709462e-07`
- train/eval anchors: `1710` / `536`

| h | tau q50 | tau q75 | tau q90 | eval base rate q75 | detectable |
|---:|---:|---:|---:|---:|---|
| 1 | 0.31284098 | 0.46348525 | 1.004552 | 0.205 | true |
| 3 | 0.85815564 | 1.1877432 | 1.7367596 | 0.183 | true |
| 5 | 1.1526871 | 1.511417 | 1.7431936 | 0.173 | true |
| 10 | 1.8885643 | 2.0319801 | 2.0897581 | 0.248 | true |

