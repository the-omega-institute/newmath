# Certificate-Guided Training

- Generated at: `2026-06-01T21:29:37.667720+00:00`
- Cost protocol: `bedc-quality-lab-default-cost-protocol`
- Formula: `task_loss + lambda_s*stability + lambda_m*margin + lambda_l*ledger + lambda_c*coverage`
- Result: `negative`
- Result note: certificate-guided candidate did not improve every tracked projection

## Records

| role | candidate | loss | quality_q | debt | cost | benefit | unlogged | critical unlogged | deterministic fallback | torch arm |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| `before` | `deterministic-baseline` | 2.204491 | -0.621742 | 0.700000 | 0.030000 | 0.108258 | 0.478261 | 0.478261 | `true` | `false` |
| `after` | `certificate-guided-sample-support` | 1.024136 | -0.568133 | 0.538133 | 0.030000 | 0.000000 | 0.000000 | 0.000000 | `true` | `false` |
| `control` | `torch-request-control` | 2.468658 | -0.860000 | 0.800000 | 0.060000 | 0.000000 | 0.478261 | 0.478261 | `false` | `true` |

## Deltas

| comparison | debt | cost | benefit | quality_q | loss |
| --- | ---: | ---: | ---: | ---: | ---: |
| `after_minus_before` | -0.161867 | 0.000000 | -0.108258 | 0.053608 | -1.180356 |
| `control_minus_before` | 0.100000 | 0.030000 | -0.108258 | -0.238258 | 0.264167 |

## Ledger Rows

- `before`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `after`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/finite-sample-support:closed:0.000000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:partial:0.038133; generalization/global-claim-boundary:closed:0.000000`
- `control`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:open:0.200000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`

## Source Artifacts

- Generation script: `scripts/run_certificate_guided_training.py`
- Canonical runner: `scripts/run_gaussian_ou_lejepa.py::run_experiment`
- Gap-ledger metric surface: `scripts/run_gaussian_ou_gap_ledger_head.py`
- Helper: `bedc_quality_lab.training.certificate_guided`
