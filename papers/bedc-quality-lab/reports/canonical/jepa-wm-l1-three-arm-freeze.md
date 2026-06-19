# JEPA-WM-L1 Three-Arm Freeze

- Generated at: `2026-06-19T07:27:48.531585+00:00`
- Venue status: `frozen`
- Decision: `ready_for_prediction`
- Prediction schema: `reports/canonical/jepa-wm-l1-three-arm-freeze.json:$.prediction_schema`
- Venue SHA: `6ee413a9bfc155f974ad45cf1a54e55385da9610cd2360f681d348a77416a7d0`

## Source Artifacts

- admission: `reports/canonical/jepa-wm-l1-admission.json` `f836b1463ac9ebc8d022c0c3a663b7fe352a2db1f71690cb3df820d5a61c88f6`
- evaluator_calibration: `reports/canonical/jepa-wm-l1-evaluator-calibration.json` `a5a171bb7163f701e8b3b04a2f31ede5c568ac036e6ca845982c309320c16e11`

## Hardgates

| gate | status | criterion |
| --- | --- | --- |
| `JWM-L1-THREE-ARM-HG1` | `pass` | admission and evaluator inputs are SHA-addressed |
| `JWM-L1-THREE-ARM-HG2` | `pass` | admission and evaluator agree on sample count |
| `JWM-L1-THREE-ARM-HG3` | `pass` | deterministic split is owned by the freeze venue |
| `JWM-L1-THREE-ARM-HG4` | `pass` | OOD labels are fixed before prediction |
| `JWM-L1-THREE-ARM-HG5` | `pass` | three stub predictions satisfy the prediction schema |
| `JWM-L1-THREE-ARM-HG6` | `pass` | bootstrap and Holm settings are frozen in the venue |
| `JWM-L1-THREE-ARM-HG7` | `pass` | leakage gates are represented as fail-closed controls |

## Not Claimed

- No three-arm model result is claimed by this freeze.
- No admission or evaluator owner semantics are changed by this freeze.
- No downstream prediction may bypass the venue artifact and prediction schema.
