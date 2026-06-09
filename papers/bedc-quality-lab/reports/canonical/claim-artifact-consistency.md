# Claim Artifact Consistency Audit

- Generated at: `2026-06-09T08:21:49.156738+00:00`
- Claim: `claim:discovery-gated-transformer`
- Status: `pass`

| gate | status | pointer | reason | expected | actual |
| --- | --- | --- | --- | --- | --- |
| `CONS-HG1` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[19]` | discovery level and verdict are coherent | `consistent` | `consistent` |
| `CONS-HG2` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[19]` | positive verdict uses the current scorecard hash | `2ae6ba313fd33b062ded8a31520e3cb56b1a2eaffba7c663069c61467ab2169c` | `2ae6ba313fd33b062ded8a31520e3cb56b1a2eaffba7c663069c61467ab2169c` |
| `CONS-HG3` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[19]` | reason taxonomy matches scorecard readiness | `consistent` | `consistent` |
| `CONS-HG4` | `pass` | `reports/canonical/claim_graph.json:$.nodes[91]` | terminal graph path reaches the DGT D4 projection | `consistent` | `consistent` |
| `CONS-HG5` | `pass` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[2]` | coverage matrix DGT cell points to the DGT owner | `consistent` | `consistent` |
| `CONS-HG6` | `pass` | `reports/canonical/high-impact-review.fingerprint.json:$.inputs.source_artifacts` | artifact hashes are current | `consistent` | `consistent` |
