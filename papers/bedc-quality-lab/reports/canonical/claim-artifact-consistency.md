# Claim Artifact Consistency Audit

- Generated at: `2026-06-16T00:19:52.227430+00:00`
- Claim: `claim:discovery-gated-transformer`
- Status: `fail`
- Paper surfaces: `3`

| gate | status | pointer | reason | expected | actual |
| --- | --- | --- | --- | --- | --- |
| `CONS-HG1` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[28]` | discovery level and verdict are coherent | `consistent` | `consistent` |
| `CONS-HG2` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[28]` | non-positive verdict has no scorecard hash promotion dependency | `not applicable` | `not applicable` |
| `CONS-HG3` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[28]` | reason taxonomy matches scorecard readiness | `consistent` | `consistent` |
| `CONS-HG4` | `fail` | `reports/canonical/claim_graph.json:$.nodes[119]` | terminal node must point to claim verdict row | `reports/canonical/claim_verdicts.jsonl:$.lines[28]` | `reports/canonical/claim_verdicts.jsonl:$.lines[25]` |
| `CONS-HG5` | `pass` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[1]` | coverage matrix DGT cell points to the DGT owner | `consistent` | `consistent` |
| `CONS-HG6` | `fail` | `reports/canonical/high-impact-review.fingerprint.json:$.inputs.source_artifacts` | high-impact review source artifact hash is stale | `reports/canonical/discovery_map.json:34badb6cced4f3fae77798c4afe669bbb2effdd4acf46690d543d48a0023ab7a` | `reports/canonical/discovery_map.json:b5c58182325933a7ef4fcc01a4ce2b19561406cfc21cc979037e2ad8158fedbf` |
| `STACK-HG1` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[28]` | non-positive verdict has no claim-first pointer requirement | `not applicable` | `not applicable` |
| `STACK-HG2` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[28]` | non-positive verdict has no claim-first owner-status requirement | `not applicable` | `not applicable` |
| `CLAIM-FIRST-HG1` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[28]` | no accepted positive row requires claim-first admission | `not applicable` | `not applicable` |
| `PAPER-HG1` | `pass` | `reports/canonical/claim-artifact-consistency.json:$.paper_surfaces` | paper artifact surface pointers and values are coherent | `consistent` | `consistent` |

## Paper Surfaces

- `quality-scorecard-release-table` `table` `reports/canonical/quality-scorecard.json:$.rows`
- `discovery-gated-transformer-evidence-figure` `figure` `reports/canonical/discovery-gated-transformer.json:$.d4_projection`
- `discovery-gated-transformer-main-claim-chain` `main_claim_chain` `reports/canonical/claim_graph.json:$.nodes[119]`
