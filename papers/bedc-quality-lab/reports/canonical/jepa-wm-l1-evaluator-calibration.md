# JEPA-WM-L1 Evaluator Calibration

- Generated at: `fixture`
- Producer: `bedc_quality_lab.tasks.jepa_wm_l1_evaluator_calibration`
- Admission owner: `bedc_quality_lab.tasks.jepa_wm_l1`
- Diagnostic route: `inspect evaluator scorer separation before any admission rerun`
- Boundary: diagnostic only; no cascade and no capability claim.

## Calibration Arms

| arm | scorer | gate | mean |
| --- | --- | --- | --- |
| `raw` | `admission.evaluate_encoded_rank_cases` | `fail` | `0.171875` |
| `frozen-probe` | `metadata-linear-probe-without-training` | `fail` | `0.1328125` |
| `oracle` | `true-label-upper-bound` | `pass` | `1.0` |
| `label-shuffle` | `shuffled-label-negative-control` | `fail` | `0.1328125` |

## Not Claimed

- No DRT or DGT cascade is triggered by this evaluator calibration.
- No downstream capability claim is produced.
- No admission verdict is changed by this evaluator calibration.
- No second owner is created for k, chance, controls, weight acquisition, or raw admission semantics.
