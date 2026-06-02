# Certificate-Guided Training

- Generated at: `2026-06-02T14:37:14.381352+00:00`
- Cost protocol: `bedc-quality-lab-default-cost-protocol`
- Formula: `task_loss + lambda_s*stability + lambda_m*margin + lambda_l*ledger + lambda_c*coverage`
- Result: `positive`
- Result note: certificate-guided candidate improved tracked debt/cost/benefit projection

## Records

| role | candidate | seed | loss | quality_q | debt | cost | benefit | unlogged | critical unlogged | deterministic fallback | torch arm |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: | ---: | --- | --- |
| `before` | `deterministic-baseline` | `25` | 2.310511 | -0.852619 | 0.940000 | 0.030000 | 0.117381 | 0.521739 | 0.521739 | `true` | `false` |
| `after` | `certificate-guided-sample-support` | `25` | 1.093851 | -0.799426 | 0.790000 | 0.030000 | 0.020574 | 0.000000 | 0.000000 | `true` | `false` |
| `control` | `torch-request-control` | `25` | 2.823691 | -1.060000 | 1.000000 | 0.060000 | 0.000000 | 0.521739 | 0.521739 | `false` | `true` |
| `before` | `deterministic-baseline` | `26` | 2.372841 | -1.008997 | 0.978997 | 0.030000 | 0.000000 | 0.486957 | 0.486957 | `true` | `false` |
| `after` | `certificate-guided-sample-support` | `26` | 1.044820 | -0.658880 | 0.790000 | 0.030000 | 0.161120 | 0.000000 | 0.000000 | `true` | `false` |
| `control` | `torch-request-control` | `26` | 3.114484 | -1.060000 | 1.000000 | 0.060000 | 0.000000 | 0.486957 | 0.486957 | `false` | `true` |
| `before` | `deterministic-baseline` | `27` | 2.251706 | -0.977004 | 0.947004 | 0.030000 | 0.000000 | 0.486957 | 0.486957 | `true` | `false` |
| `after` | `certificate-guided-sample-support` | `27` | 1.183804 | -0.838883 | 0.808883 | 0.030000 | 0.000000 | 0.043478 | 0.000000 | `true` | `false` |
| `control` | `torch-request-control` | `27` | 2.544606 | -0.813085 | 1.000000 | 0.060000 | 0.246915 | 0.486957 | 0.486957 | `false` | `true` |

## Deltas

| comparison | debt | cost | benefit | quality_q | loss |
| --- | ---: | ---: | ---: | ---: | ---: |
| `after_minus_before` | -0.159040 | 0.000000 | 0.021438 | 0.180478 | -1.204195 |
| `control_minus_before` | 0.044666 | 0.030000 | 0.043178 | -0.031488 | 0.515907 |

## Scope

- Claimed scope: `certificate-guided before-after-control projection on paired local seeds`
- Seeds: `25, 26, 27`
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
| `after_minus_before` | `quality_q_delta` | `ok` | 3 | 0.180478 | 0.007425 | 0.353530 |
| `control_minus_before` | `quality_q_delta` | `ok` | 3 | -0.031488 | -0.242439 | 0.179463 |

## Claim Gate

- Mechanical quality gate: `true`
- Required quality_q CI lower > 0: `true`
- Observed quality_q CI lower: `0.007425`
- Paired CI status: `ok`
- Audit improvement tradeoff: `false`
- Blockers: `none`

## Not Claimed

- formal BEDC closure is not claimed by this lab-local runner
- global optimizer behavior is not claimed by this lab-local runner
- positive quality improvement is not claimed unless the paired after-minus-before quality_q CI lower bound is above zero

## Ledger Rows

- `before`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `after`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:partial:0.050000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `control`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:open:0.200000; verification/theorem3-bound-margin:partial:0.107466; generalization/global-claim-boundary:closed:0.000000`
- `before`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:partial:0.038997; generalization/global-claim-boundary:closed:0.000000`
- `after`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:partial:0.050000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`
- `control`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:open:0.200000; verification/theorem3-bound-margin:open:0.200000; generalization/global-claim-boundary:closed:0.000000`
- `before`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:partial:0.007004; generalization/global-claim-boundary:closed:0.000000`
- `after`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:partial:0.050000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:partial:0.100000; verification/theorem3-bound-margin:partial:0.018883; generalization/global-claim-boundary:closed:0.000000`
- `control`: `source/source-coverage:open:0.180000; source/mixing-family-coverage:open:0.220000; source/latent-distribution-gaussianity:closed:0.000000; source/distribution-family-coverage:open:0.240000; source/finite-sample-support:open:0.200000; source/transition-isotropy:closed:0.000000; classifier/optimizer-certificate:open:0.200000; verification/theorem3-bound-margin:closed:0.000000; generalization/global-claim-boundary:closed:0.000000`

## Source Artifacts

- Generation script: `scripts/run_certificate_guided_training.py`
- Canonical runner: `scripts/run_gaussian_ou_lejepa.py::run_experiment`
- Gap-ledger metric surface: `scripts/run_gaussian_ou_gap_ledger_head.py`
- Helper: `bedc_quality_lab.training.certificate_guided`
