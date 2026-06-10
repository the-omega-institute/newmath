# Claim Artifact Consistency Audit

- Generated at: `2026-06-09T08:21:49.156738+00:00`
- Claim: `claim:discovery-gated-transformer`
- Status: `pass`

| gate | status | pointer | reason | expected | actual |
| --- | --- | --- | --- | --- | --- |
| `CONS-HG1` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[20]` | discovery level and verdict are coherent | `consistent` | `consistent` |
| `CONS-HG2` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[20]` | positive verdict uses the current scorecard hash | `0585ba8713d21026d19a86498a970c0f910b08f08aa6cbd462585002bff1e930` | `0585ba8713d21026d19a86498a970c0f910b08f08aa6cbd462585002bff1e930` |
| `CONS-HG3` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[20]` | reason taxonomy matches scorecard readiness | `consistent` | `consistent` |
| `CONS-HG4` | `pass` | `reports/canonical/claim_graph.json:$.nodes[98]` | terminal graph path uses Core claim verdict row | `consistent` | `consistent` |
| `CONS-HG5` | `pass` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[1]` | coverage matrix DGT cell points to the DGT owner | `consistent` | `consistent` |
| `CONS-HG6` | `pass` | `reports/canonical/high-impact-review.fingerprint.json:$.inputs.source_artifacts` | artifact hashes are current | `consistent` | `consistent` |
