# Model Comparison

- Generated at: `2026-06-08T04:43:38.290622+00:00`
- Artifact: `bedc-quality-lab:model-comparison`
- Schema: `bedc-quality-lab:model-comparison`
- Status: `not_ready`
- Ranking key: `quality_q, JetCoverage`

## Models

| model | status | owner | metrics |
| --- | --- | --- | --- |
| `base_transformer` | `missing_source` | `None` | `0/12` |
| `ledger-aware-transformer` | `ready` | `reports/canonical/ledger-aware-transformer.json:$` | `12/12` |
| `certificate-gated-attention` | `ready` | `reports/canonical/certificate-gated-attention.json:$` | `12/12` |
| `discovery-regularized-training` | `ready` | `reports/canonical/discovery-regularized-training.json:$` | `12/12` |
| `mechanism-seeking-network` | `ready` | `reports/canonical/mechanism-seeking-network.json:$` | `12/12` |
| `DGT candidate` | `ready` | `reports/canonical/discovery-gated-transformer.json:$` | `12/12` |
| `matched-random structural control` | `missing_source` | `None` | `0/12` |

## Hardgates

| gate | status | reason |
| --- | --- | --- |
| `CMP-HG1` | `pass` | parameter-matched baseline pointer resolves through the ledger-aware owner |
| `CMP-HG2` | `pass` | compute-matched cost pointer resolves for candidate comparison |
| `CMP-HG3` | `fail` | matched-random structural control has a canonical owner pointer; fail-closed |
| `CMP-HG4` | `pass` | every non-missing model row resolves to a canonical owner |
| `CMP-HG5` | `pass` | claim-specific ordering key pointers resolve before ordering is emitted |
