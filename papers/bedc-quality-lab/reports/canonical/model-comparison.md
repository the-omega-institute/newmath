# Model Comparison

- Generated at: `2026-06-12T14:49:10.626178+00:00`
- Artifact: `bedc-quality-lab:model-comparison`
- Schema: `bedc-quality-lab:model-comparison`
- Status: `ready`
- Ranking key: `quality_q, JetCoverage`

## Models

| model | role | status | quality_q | JetCoverage | UER reduction |
| --- | --- | --- | ---: | ---: | ---: |
| `dgt` | DGT source row | `resolved` | 0.760089 | 0.825499 | 0.337379 |
| `base_transformer` | base_transformer control row | `resolved` | 0.507174 | 0.352408 | 0.030671 |
| `matched_random_structural_control` | matched_random_structural_control control row | `resolved` | 0.438873 | 0.314720 | 0.005202 |
| `ledger-aware-transformer` | ledger-aware transformer canonical owner row | `ready` | 0.437487 | 0.315740 | 0.005319 |
| `certificate-gated-attention` | certificate-gated attention canonical owner row | `ready` | 0.438621 | 0.316938 | 0.004392 |
| `discovery-regularized-training` | discovery-regularized training canonical owner row | `ready` | 0.441845 | 0.312076 | 0.005171 |
| `mechanism-seeking-network` | mechanism-seeking network canonical owner row | `ready` | 0.436793 | 0.316682 | 0.005120 |

## Comparison Semantics

| comparison | type | metric provenance | evidence chain |
| --- | --- | --- | --- |
| `dgt_control_projection` | `deterministic_projection` | `deterministic_projection` | `False` |

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
| `MC-HG11` | `pass` | comparison rows carry exactly one validated semantic object |
| `MC-HG12` | `pass` | comparison semantics point to the evidence provenance owner row |
| `MC-HG13` | `pass` | deterministic projection rows cannot enter measured-training evidence chains |
| `MC-HG14` | `pass` | projection rows carry trained-model claim boundaries |

## Not Claimed

- No production deployment readiness is claimed.
- No global model superiority claim is made.
- No terminal verdict or winner is emitted.
- The comparison is a deterministic toy owner-projection lane only.
- No trained-model evidence claim from projection artifacts.
