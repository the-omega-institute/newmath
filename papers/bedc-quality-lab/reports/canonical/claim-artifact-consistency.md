# Claim Artifact Consistency Audit

- Generated at: `2026-06-11T20:43:54.611653+00:00`
- Claim: `claim:discovery-gated-transformer`
- Status: `pass`

| gate | status | pointer | reason | expected | actual |
| --- | --- | --- | --- | --- | --- |
| `CONS-HG1` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[21]` | discovery level and verdict are coherent | `consistent` | `consistent` |
| `CONS-HG2` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[21]` | positive verdict uses the current scorecard hash | `ccd94abf73f265ddebccc296e811c87dd34393fc700a9da9df1c050d5eaa9687` | `ccd94abf73f265ddebccc296e811c87dd34393fc700a9da9df1c050d5eaa9687` |
| `CONS-HG3` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[21]` | reason taxonomy matches scorecard readiness | `consistent` | `consistent` |
| `CONS-HG4` | `pass` | `reports/canonical/claim_graph.json:$.nodes[105]` | terminal graph path uses Core claim verdict row | `consistent` | `consistent` |
| `CONS-HG5` | `pass` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[1]` | coverage matrix DGT cell points to the DGT owner | `consistent` | `consistent` |
| `CONS-HG6` | `pass` | `reports/canonical/high-impact-review.fingerprint.json:$.inputs.source_artifacts` | artifact hashes are current | `consistent` | `consistent` |
