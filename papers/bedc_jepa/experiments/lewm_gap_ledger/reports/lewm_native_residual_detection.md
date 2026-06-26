# Native Residual Detection

- status: `ok`
- decision: `failed_parity_is_upper_bound`
- skeleton anchor E h=1 q75 AUROC: `0.738515205860` (expected `0.738515205860`, abs delta `0`)

## AUROC vs Post-Hoc

| arm | objective | h=1 native AUROC [95% CI] | h=1 post-hoc AUROC [95% CI] | h=5 native AUROC [95% CI] | h=5 post-hoc AUROC [95% CI] |
|---|---|---:|---:|---:|---:|
| R-reg | Huber(log mean_err_to_h[h]) dual-head | `0.740278` [`0.697397`, `0.782092`] | `0.737486` [`0.698811`, `0.774685`] | `0.717287` [`0.663746`, `0.761292`] | `0.710364` [`0.666395`, `0.750271`] |
| R-rank | within-episode pairwise logistic ranking over mean_err_to_h[h] dual-head | `0.787602` [`0.746652`, `0.826938`] | `0.737486` [`0.698811`, `0.774685`] | `0.732552` [`0.661559`, `0.794993`] | `0.710364` [`0.666395`, `0.750271`] |
| R-multitask-lambda0p25 | BCE horizon + 0.25*Huber(log mean_err) + pairwise rank | `0.775389` [`0.732496`, `0.818875`] | `0.737486` [`0.698811`, `0.774685`] | `0.696148` [`0.630329`, `0.749600`] | `0.710364` [`0.666395`, `0.750271`] |
| R-multitask-lambda1p0 | BCE horizon + 1.0*Huber(log mean_err) + pairwise rank | `0.779286` [`0.740712`, `0.818681`] | `0.737486` [`0.698811`, `0.774685`] | `0.692929` [`0.627709`, `0.747879`] | `0.710364` [`0.666395`, `0.750271`] |

## Spearman Attachment

| arm | h=1 Spearman(score, mean_err) | h=5 Spearman(score, mean_err) |
|---|---:|---:|
| R-reg | `0.519573` [`0.461641`, `0.574598`] | `0.492858` [`0.416476`, `0.561027`] |
| R-rank | `0.626001` [`0.573432`, `0.673069`] | `0.540279` [`0.451586`, `0.625999`] |
| R-multitask-lambda0p25 | `0.593432` [`0.539759`, `0.637624`] | `0.471842` [`0.369314`, `0.566568`] |
| R-multitask-lambda1p0 | `0.580547` [`0.536924`, `0.622512`] | `0.488485` [`0.392054`, `0.574783`] |

## Decision

- positive(B breakthrough): `False`
- best native arm: `R-rank` h=`1` AUROC=`0.787602`
- reason: best native residual arm improves only by point estimate or not at all; its CI overlaps the corresponding post-hoc CI

## Not Claimed
- Spearman is reported only as an attachment and is not used for the B breakthrough decision
- single latent export and single checkpoint; episode bootstrap is not independent world-seed replication
- post-hoc control is the frozen B_posthoc_horizon value from g2n_matrix_completion, not retuned here
- lambda is limited to the predeclared {0.25, 1.0}; no hyperparameter tuning or model selection beyond reporting best observed arm
- no planning/control benefit is claimed
