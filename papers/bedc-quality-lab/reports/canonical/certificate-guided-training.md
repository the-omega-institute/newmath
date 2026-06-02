# Certificate-Guided Training

- Generated at: `2026-06-02T13:02:19.731086+00:00`
- Cost protocol: `bedc-quality-lab-default-cost-protocol`
- Formula: `task_loss + lambda_s*stability + lambda_m*margin + lambda_l*ledger + lambda_c*coverage`
- Result: `negative`
- Result note: certificate-guided candidate did not improve every tracked projection

## Records

| role | candidate | loss | quality_q | debt | cost | benefit | unlogged | critical unlogged | deterministic fallback | torch arm |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| `before` | `deterministic-baseline` | 2.310511 | -0.852619 | 0.940000 | 0.030000 | 0.117381 | 0.521739 | 0.521739 | `true` | `false` |
| `after` | `certificate-guided-sample-support` | 1.093851 | -0.799426 | 0.790000 | 0.030000 | 0.020574 | 0.000000 | 0.000000 | `true` | `false` |
| `control` | `torch-request-control` | 2.823691 | -1.060000 | 1.000000 | 0.060000 | 0.000000 | 0.521739 | 0.521739 | `false` | `true` |

## Deltas

| comparison | debt | cost | benefit | quality_q | loss |
| --- | ---: | ---: | ---: | ---: | ---: |
| `after_minus_before` | -0.150000 | 0.000000 | -0.096806 | 0.053194 | -1.216661 |
| `control_minus_before` | 0.060000 | 0.030000 | -0.117381 | -0.207381 | 0.513179 |

## Ledger Rows

- `before`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `after`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:partial:0.050000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `control`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:open:0.200000; verification/theorem3-bound-margin:partial:0.107466; generalization/global-claim-boundary:closed:0.000000`

## Source Artifacts

- Generation script: `scripts/run_certificate_guided_training.py`
- Canonical runner: `scripts/run_gaussian_ou_lejepa.py::run_experiment`
- Gap-ledger metric surface: `scripts/run_gaussian_ou_gap_ledger_head.py`
- Helper: `bedc_quality_lab.training.certificate_guided`
