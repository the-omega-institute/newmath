# Model Comparison

- Generated at: `2026-06-08T16:01:18.490477+00:00`
- Artifact: `bedc-quality-lab:model-comparison`
- Schema: `bedc-quality-lab:model-comparison`
- Status: `ready`
- Ranking key: `quality_q, JetCoverage`

## Owners

| owner | role | status | quality_q | JetCoverage | UER reduction |
| --- | --- | --- | ---: | ---: | ---: |
| `dgt` | DGT source row | `resolved` | 0.760089 | 0.825499 | 0.337379 |
| `base_transformer` | base_transformer control row | `resolved` | 0.507174 | 0.352408 | 0.030671 |
| `matched_random_structural_control` | matched_random_structural_control control row | `resolved` | 0.438873 | 0.314720 | 0.005202 |

## Hardgates

| gate | status | reason |
| --- | --- | --- |
| `MC-HG1` | `pass` | required source and control owners are present |
| `MC-HG2` | `pass` | evidence envelopes and claim capsules resolve |
| `MC-HG3` | `pass` | owners share the same nine-surface suite |
| `MC-HG4` | `pass` | owners expose the same twelve metric keys |
| `MC-HG5` | `pass` | parameter counts are matched |
| `MC-HG6` | `pass` | compute budgets are matched |
| `MC-HG7` | `pass` | DGT quality_q exceeds the base-transformer CI-low proxy |
| `MC-HG8` | `pass` | DGT UER reduction exceeds matched-random structural control |
| `MC-HG9` | `pass` | matched-random structural control has classifier_shift_count zero |
| `MC-HG10` | `pass` | non-claim boundary excludes production and global-superiority |

## Not Claimed

- No production deployment readiness is claimed.
- No global model superiority claim is made.
- No terminal verdict or winner is emitted.
- The comparison is a deterministic toy owner-projection lane only.
