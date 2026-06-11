# Claim Artifact Consistency Audit

- Generated at: `2026-06-11T20:45:19.422516+00:00`
- Claim: `claim:discovery-gated-transformer`
- Status: `fail`

| gate | status | pointer | reason | expected | actual |
| --- | --- | --- | --- | --- | --- |
| `CONS-HG1` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[22]` | discovery level and verdict are coherent | `consistent` | `consistent` |
| `CONS-HG2` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[22]` | positive verdict uses the current scorecard hash | `3e8b37edacf9bea2e5d2b9cb595b496e9ad9e4dbdc039c2c92d0e0608ff31fb0` | `3e8b37edacf9bea2e5d2b9cb595b496e9ad9e4dbdc039c2c92d0e0608ff31fb0` |
| `CONS-HG3` | `pass` | `reports/canonical/claim_verdicts.jsonl:$.lines[22]` | reason taxonomy matches scorecard readiness | `consistent` | `consistent` |
| `CONS-HG4` | `fail` | `reports/canonical/claim_graph.json:$.nodes[103]` | terminal node must point to claim verdict row | `reports/canonical/claim_verdicts.jsonl:$.lines[22]` | `reports/canonical/claim_verdicts.jsonl:$.lines[21]` |
| `CONS-HG5` | `pass` | `reports/canonical/discovery_map.json:$.coverage_matrix.cells[1]` | coverage matrix DGT cell points to the DGT owner | `consistent` | `consistent` |
| `CONS-HG6` | `fail` | `reports/canonical/high-impact-review.fingerprint.json:$.inputs.source_artifacts` | high-impact review source artifact hash is stale | `reports/canonical/discovery-gated-transformer.json:7f9cce0aa3917a22911ced04db12c5e49cf2f41b098255f7747e86fce1cba47d` | `reports/canonical/discovery-gated-transformer.json:0cc7a2c787ad979ccb0c6f8636bb1c6b428d2d878c86cf7967db92717e890216` |
