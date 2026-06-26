# Ledger-Aware Transformer

- Generated at: `2026-06-05T15:14:26.399733+00:00`
- Schema: `bedc.model.ledger_aware_transformer`
- Surface count: `6`
- OOD surface count: `6`
- UER reduction: `0.090278`
- False alarm delta: `-0.034722`
- Discovery signal: `D5-O`
- Failed gate: `None`
- Claim capsule pointer: `$.claim_capsule_ref.capsule`
- Mechanism certificate pointer: `$.mechanism_certificate`

## Hardgates

| gate | status | pointer |
| --- | --- | --- |
| `LAT-HG1` | `pass` | `$.records` |
| `LAT-HG2` | `pass` | `$.ledger.rows` |
| `LAT-HG3` | `pass` | `$.aggregate_metrics.uer_reduction` |
| `LAT-HG4` | `pass` | `$.matched_random_control.control_positive_discovery` |
| `LAT-HG5` | `pass` | `$.forbidden_claim_term_audit.status` |
| `LAT-HG6` | `pass` | `$.torch_training_evidence.protocol` |
| `LAT-HG7` | `pass` | `$.mechanism_certificate` |
| `LAT-HG8` | `pass` | `$.compute_matched_baseline` |

## Records

| surface | learned UER | matched-random UER | UER delta | false alarm delta |
| --- | ---: | ---: | ---: | ---: |
| `delayed_recall` | 0.020833 | 0.083333 | 0.062500 | -0.229167 |
| `compositional_rules` | 0.000000 | 0.291667 | 0.291667 | -0.145833 |
| `synthetic_tool_use` | 0.020833 | 0.208333 | 0.187500 | -0.187500 |
| `toy_safety_boundary` | 0.000000 | 0.000000 | 0.000000 | 0.000000 |
| `toy_planning` | 0.000000 | 0.000000 | 0.000000 | 0.312500 |
| `compression_preservation` | 0.000000 | 0.000000 | 0.000000 | 0.041667 |

## Component Ablation

| component | status | UER delta | claim eligible |
| --- | --- | ---: | --- |
| `ledger_head` | `accepted` | 0.090278 | `True` |
| `gap_head` | `accepted` | 0.070417 | `True` |
| `route_head` | `rejected` | 0.000000 | `False` |

## Canonical Pointers

- Scope pointer: `$.applicability_boundary`
- Cost pointer: `$.source_artifacts.cost_protocol`
- Positive claim pointer: `$.positive_claim`
- Control pointer: `$.control_protocol`
- Parameter-matched baseline pointer: `$.parameter_matched_baseline`
- Compute-matched baseline pointer: `$.compute_matched_baseline`
- Mechanism certificate pointer: `$.mechanism_certificate`
- Discovery signal pointer: `$.discovery_map_signal`
- Torch evidence pointer: `$.torch_training_evidence`
