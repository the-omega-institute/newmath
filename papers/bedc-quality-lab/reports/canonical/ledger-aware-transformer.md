# Ledger-Aware Transformer

- Generated at: `2026-06-05T15:14:26.399733+00:00`
- Schema: `bedc.model.ledger_aware_transformer`
- Surface count: `3`
- OOD surface count: `3`
- UER reduction: `0.180555`
- False alarm delta: `-0.1875`
- Claim capsule pointer: `$.claim_capsule_ref.capsule`

## Records

| surface | learned UER | matched-random UER | UER delta | false alarm delta |
| --- | ---: | ---: | ---: | ---: |
| `copy_shift` | 0.020833 | 0.083333 | 0.062500 | -0.229167 |
| `parity_route` | 0.000000 | 0.291667 | 0.291667 | -0.145833 |
| `sparse_recall` | 0.020833 | 0.208333 | 0.187500 | -0.187500 |

## Canonical Pointers

- Scope pointer: `$.applicability_boundary`
- Cost pointer: `$.source_artifacts.cost_protocol`
- Positive claim pointer: `$.positive_claim`
- Control pointer: `$.control_protocol`
