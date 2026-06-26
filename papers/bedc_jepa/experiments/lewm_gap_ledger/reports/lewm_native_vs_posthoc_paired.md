# Native vs Post-Hoc Paired AUROC

- status: `ok`
- B verdict: `B_positive`
- rule: B positive iff R-rank paired delta AUROC(h=1) CI95_low > 0; otherwise B parity-bound.
- E skeleton anchor h=1: `0.738515205859875`
- R-rank anchor h=1: `0.787602248908462`

## Paired Delta AUROC

| arm | h | native AUROC | post-hoc AUROC | delta native-posthoc [95% CI] | decision |
|---|---:|---:|---:|---:|---|
| R-reg | 1 | `0.740278` | `0.737486` | `0.002792` [`-0.050630`, `0.055503`] | `not_separated` |
| R-reg | 5 | `0.717287` | `0.710364` | `0.006923` [`-0.043749`, `0.059813`] | `not_separated` |
| R-rank | 1 | `0.787602` | `0.737486` | `0.050116` [`0.004274`, `0.100087`] | `positive` |
| R-rank | 5 | `0.732552` | `0.710364` | `0.022187` [`-0.041996`, `0.091608`] | `not_separated` |
| R-multitask-lambda0p25 | 1 | `0.775389` | `0.737486` | `0.037903` [`-0.012382`, `0.093176`] | `not_separated` |
| R-multitask-lambda0p25 | 5 | `0.696148` | `0.710364` | `-0.014217` [`-0.077213`, `0.050104`] | `not_separated` |
| R-multitask-lambda1p0 | 1 | `0.779286` | `0.737486` | `0.041800` [`-0.003740`, `0.092809`] | `not_separated` |
| R-multitask-lambda1p0 | 5 | `0.692929` | `0.710364` | `-0.017436` [`-0.075584`, `0.044428`] | `not_separated` |

## Prior Independent CI

Round2-B independent-CI results are retained as prior context; this report adds the paired comparison on the same eval episodes.

| arm | h | native AUROC [CI] | post-hoc AUROC [CI] | independent CI separates |
|---|---:|---:|---:|---|
| R-reg | 1 | `0.740278` [`0.697397`, `0.782092`] | `0.737486` [`0.698811`, `0.774685`] | `False` |
| R-reg | 5 | `0.717287` [`0.663746`, `0.761292`] | `0.710364` [`0.666395`, `0.750271`] | `False` |
| R-rank | 1 | `0.787602` [`0.746652`, `0.826938`] | `0.737486` [`0.698811`, `0.774685`] | `False` |
| R-rank | 5 | `0.732552` [`0.661559`, `0.794993`] | `0.710364` [`0.666395`, `0.750271`] | `False` |
| R-multitask-lambda0p25 | 1 | `0.775389` [`0.732496`, `0.818875`] | `0.737486` [`0.698811`, `0.774685`] | `False` |
| R-multitask-lambda0p25 | 5 | `0.696148` [`0.630329`, `0.749600`] | `0.710364` [`0.666395`, `0.750271`] | `False` |
| R-multitask-lambda1p0 | 1 | `0.779286` [`0.740712`, `0.818681`] | `0.737486` [`0.698811`, `0.774685`] | `False` |
| R-multitask-lambda1p0 | 5 | `0.692929` [`0.627709`, `0.747879`] | `0.710364` [`0.666395`, `0.750271`] | `False` |

## Not Claimed
- Round2-B independent-CI not_positive result is retained and cited as prior context.
- This report only changes the comparison statistic to the paired AUROC delta on the same eval episodes.
- single checkpoint and single latent export; no world-seed replication is claimed.
- R-rank was reproduced from the Round2-B seed and hyperparameters, not retrained to a better seed.
- post-hoc horizon reader uses the same split and frozen protocol; it is rebuilt only to expose per-anchor scores.
- No planning or control benefit is claimed.
