# Claim Artifact Consistency Audit

- Generated at: `2026-06-12T09:33:41.573506+00:00`
- Claim: `claim:discovery-gated-transformer`
- Status: `pass`

| gate | status | pointer | reason | expected | actual |
| --- | --- | --- | --- | --- | --- |
| `CONS-HG1` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[24]` | discovery level and verdict are coherent | `consistent` | `consistent` |
| `CONS-HG2` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[24]` | non-positive verdict has no scorecard hash promotion dependency | `not applicable` | `not applicable` |
| `CONS-HG3` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[24]` | reason taxonomy matches scorecard readiness | `consistent` | `consistent` |
| `CONS-HG4` | `pass` | `reports/canonical/claim_graph.json:$.nodes[116]` | terminal graph path uses Core claim verdict row | `consistent` | `consistent` |
| `CONS-HG5` | `pass` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[1]` | coverage matrix DGT cell points to the DGT owner | `consistent` | `consistent` |
| `CONS-HG6` | `pass` | `reports/canonical/high-impact-review.fingerprint.json:$.inputs.source_artifacts` | artifact hashes are current | `consistent` | `consistent` |
