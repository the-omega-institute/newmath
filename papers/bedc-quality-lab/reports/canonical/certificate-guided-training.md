# Certificate-Guided Training

- Generated at: `2026-06-03T05:12:47.429143+00:00`
- Cost protocol: `bedc-quality-lab-default-cost-protocol`
- Formula: `task_loss + lambda_s*stability + lambda_m*margin + lambda_l*ledger + lambda_c*coverage`
- Result: `negative`
- Result note: certificate-guided candidate did not improve every tracked projection

## Records

| role | candidate | seed | loss | quality_q | debt | cost | benefit | unlogged | critical unlogged | deterministic fallback | torch arm |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| `before` | `deterministic-baseline` | `18` | 2.520535 | -0.879052 | 0.940000 | 0.030000 | 0.090948 | 0.539130 | 0.539130 | `true` | `false` |
| `after` | `certificate-guided-sample-support` | `18` | 1.249754 | -0.827207 | 0.797207 | 0.030000 | 0.000000 | 0.043478 | 0.000000 | `true` | `false` |
| `control` | `torch-request-control` | `18` | 3.829161 | -1.060000 | 1.000000 | 0.060000 | 0.000000 | 0.539130 | 0.539130 | `false` | `true` |
| `before` | `deterministic-baseline` | `25` | 2.450330 | -0.852619 | 0.940000 | 0.030000 | 0.117381 | 0.521739 | 0.521739 | `true` | `false` |
| `after` | `certificate-guided-sample-support` | `25` | 1.165200 | -0.799426 | 0.790000 | 0.030000 | 0.020574 | 0.000000 | 0.000000 | `true` | `false` |
| `control` | `torch-request-control` | `25` | 3.174606 | -1.060000 | 1.000000 | 0.060000 | 0.000000 | 0.521739 | 0.521739 | `false` | `true` |
| `before` | `deterministic-baseline` | `36` | 2.139737 | -0.611910 | 0.940000 | 0.030000 | 0.358090 | 0.486957 | 0.486957 | `true` | `false` |
| `after` | `certificate-guided-sample-support` | `36` | 1.116908 | -0.598924 | 0.790000 | 0.030000 | 0.221076 | 0.026087 | 0.000000 | `true` | `false` |
| `control` | `torch-request-control` | `36` | 2.836331 | -0.672620 | 1.000000 | 0.060000 | 0.387380 | 0.486957 | 0.486957 | `false` | `true` |

## Deltas

| comparison | debt | cost | benefit | quality_q | loss |
| --- | ---: | ---: | ---: | ---: | ---: |
| `after_minus_before` | -0.147598 | 0.000000 | -0.108256 | 0.039342 | -1.192913 |
| `control_minus_before` | 0.060000 | 0.030000 | -0.059679 | -0.149679 | 0.909832 |

## Scope

- Claimed scope: `certificate-guided before-after-control projection on paired local seeds`
- Seeds: `18, 25, 36`
- Split fingerprint key: `split_fingerprint`

## Cost Protocol

- Name: `bedc-quality-lab-default-cost-protocol`
- Formula: `quality_q`

## Before-After-Control

- Records present: `true`
- Shared cost protocol: `true`
- Shared split fingerprint class: `true`

## Paired-Seed CI

| comparison | metric | status | n | mean | ci95 low | ci95 high |
| --- | --- | --- | ---: | ---: | ---: | ---: |
| `after_minus_before` | `quality_q_delta` | `ok` | 3 | 0.039342 | 0.013502 | 0.065182 |
| `control_minus_before` | `quality_q_delta` | `ok` | 3 | -0.149679 | -0.238143 | -0.061216 |

## Claim Gate

- Mechanical quality gate: `false`
- Required quality_q CI lower > 0: `true`
- Observed quality_q CI lower: `0.013502`
- Paired CI status: `ok`
- Audit improvement tradeoff: `true`
- Blockers: `audit-improvement-tradeoff`

## Not Claimed

- formal BEDC closure is not claimed by this lab-local runner
- global optimizer behavior is not claimed by this lab-local runner
- positive quality improvement is not claimed unless the paired after-minus-before quality_q CI lower bound is above zero
- positive quality wording is not claimed for debt reduction paired with benefit decline

## Ledger Rows

- `before`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `after`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:partial:0.050000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:partial:0.007207; generalization/global-claim-boundary:closed:0.000000`
- `control`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:open:0.200000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `before`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `after`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:partial:0.050000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `control`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:open:0.200000; verification/theorem3-bound-margin:partial:0.107466; generalization/global-claim-boundary:closed:0.000000`
- `before`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `after`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:partial:0.050000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `control`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:open:0.200000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`

## Source Artifacts

- Generation script: `scripts/run_certificate_guided_training.py`
- Canonical runner: `scripts/run_gaussian_ou_lejepa.py::run_experiment`
- Gap-ledger metric surface: `scripts/run_gaussian_ou_gap_ledger_head.py`
- Helper: `bedc_quality_lab.training.certificate_guided`
