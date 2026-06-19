# JEPA-WM-L1 OOD Adjudication

- Generated at: `2026-06-18T00:00:00+00:00`
- Producer: `bedc_quality_lab.tasks.jepa_wm_l1_ood_adjudication`
- Verdict: `success`
- Reason: base arm clears null by the preregistered success margin on every OOD split

## Fixed Splits

- `heldout-dynamics`: `success_candidate` (base-low minus null-high `0.086`)
- `goal-remap`: `success_candidate` (base-low minus null-high `0.06`)
- `temporal-gap`: `success_candidate` (base-low minus null-high `0.061`)
- `distractor-clutter`: `success_candidate` (base-low minus null-high `0.055`)

## Hardgates

| gate | status |
| --- | --- |
| `BUDGET` | `pass` |
| `ARMS` | `pass` |
| `SPLITS` | `pass` |
| `METRICS` | `pass` |
| `CONTROLS` | `pass` |

## Not Claimed

- No JEPA-WM-L2 or higher OOD result.
- No global world-model superiority claim.
- No DGT tiny-sequence control extension.
- No package-root task ownership claim.
- No production deployment claim.
