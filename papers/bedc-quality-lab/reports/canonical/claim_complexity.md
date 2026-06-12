# Claim Complexity

- Artifact: `bedc-quality-lab:claim-complexity`
- Generated at: `2026-06-11T08:40:12.594518+00:00`
- Role: `artifact-only evidence`

## Hardgates

| gate | status | reason |
| --- | --- | --- |
| `CC-HG1` | `pass` | `all evidence and verdict pointers resolve` |
| `CC-HG2` | `pass` | `D5-M rows carry all required dimensions` |
| `CC-HG3` | `pass` | `D4 rows pass through without promotion authority` |

## Rows

| claim | score | verdict ref | dimensions |
| --- | --- | --- | --- |
| `claim:mixing-family-sweep` | `2` | `reports/canonical/claim_verdicts.jsonl:$.lines[0]` | `assumption_complexity=1, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:anisotropic-ou-sweep` | `2` | `reports/canonical/claim_verdicts.jsonl:$.lines[1]` | `assumption_complexity=1, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:gap-head-on-h` | `12` | `reports/canonical/claim_verdicts.jsonl:$.lines[2]` | `assumption_complexity=4, proof_burden=2, evidence_burden=3, backend_coupling=2, witness_exposure=1, revocation_fragility=0` |
| `claim:gap-head-discovery` | `10` | `reports/canonical/claim_verdicts.jsonl:$.lines[3]` | `assumption_complexity=4, proof_burden=2, evidence_burden=3, backend_coupling=1, witness_exposure=0, revocation_fragility=0` |
| `claim:gap-head-ablation` | `6` | `reports/canonical/claim_verdicts.jsonl:$.lines[4]` | `assumption_complexity=2, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=1, revocation_fragility=2` |
| `claim:irreducibility-report` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[5]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:ledger-aware-transformer` | `12` | `reports/canonical/claim_verdicts.jsonl:$.lines[6]` | `assumption_complexity=5, proof_burden=2, evidence_burden=3, backend_coupling=2, witness_exposure=0, revocation_fragility=0` |
| `claim:certificate-gated-attention` | `10` | `reports/canonical/claim_verdicts.jsonl:$.lines[7]` | `assumption_complexity=4, proof_burden=2, evidence_burden=3, backend_coupling=1, witness_exposure=0, revocation_fragility=0` |
| `claim:gap-head-threshold-frontier` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[8]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:gap-head-transfer-atlas` | `12` | `reports/canonical/claim_verdicts.jsonl:$.lines[9]` | `assumption_complexity=5, proof_burden=2, evidence_burden=3, backend_coupling=1, witness_exposure=0, revocation_fragility=1` |
| `claim:gap-head-attribution-capsule` | `2` | `reports/canonical/claim_verdicts.jsonl:$.lines[10]` | `assumption_complexity=0, proof_burden=0, evidence_burden=2, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:nongaussian-distribution-sweep` | `2` | `reports/canonical/claim_verdicts.jsonl:$.lines[11]` | `assumption_complexity=1, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:certificate-guided-training` | `7` | `reports/canonical/claim_verdicts.jsonl:$.lines[12]` | `assumption_complexity=2, proof_burden=0, evidence_burden=2, backend_coupling=0, witness_exposure=1, revocation_fragility=2` |
| `claim:certificate-guided-discovery` | `6` | `reports/canonical/claim_verdicts.jsonl:$.lines[13]` | `assumption_complexity=2, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=1, revocation_fragility=2` |
| `claim:sigreg-training-proxy` | `3` | `reports/canonical/claim_verdicts.jsonl:$.lines[14]` | `assumption_complexity=1, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=1` |
| `claim:sigreg-mini-grid` | `5` | `reports/canonical/claim_verdicts.jsonl:$.lines[15]` | `assumption_complexity=2, proof_burden=1, evidence_burden=2, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:discovery-regularized-training` | `12` | `reports/canonical/claim_verdicts.jsonl:$.lines[16]` | `assumption_complexity=6, proof_burden=2, evidence_burden=3, backend_coupling=1, witness_exposure=0, revocation_fragility=0` |
| `claim:mechanism-seeking-network` | `10` | `reports/canonical/claim_verdicts.jsonl:$.lines[17]` | `assumption_complexity=4, proof_burden=2, evidence_burden=3, backend_coupling=1, witness_exposure=0, revocation_fragility=0` |
| `claim:mechanism-dna` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[18]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:dgt-l0-controls` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[19]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:winnability-certificates` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[20]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:structural-generalization-splits` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[21]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:dgt-base-undertraining-audit` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[22]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:discovery-gated-transformer` | `12` | `reports/canonical/claim_verdicts.jsonl:$.lines[23]` | `assumption_complexity=6, proof_burden=2, evidence_burden=3, backend_coupling=1, witness_exposure=0, revocation_fragility=0` |
| `claim:dgt-neural-ablation` | `4` | `reports/canonical/claim_verdicts.jsonl:$.lines[24]` | `assumption_complexity=0, proof_burden=0, evidence_burden=3, backend_coupling=1, witness_exposure=0, revocation_fragility=0` |
| `claim:dgt-ablation-null-decomposition` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[25]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:dgt-component-redundancy-audit` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[26]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:dgt-model-card` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[27]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:order-k-benchmark` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[28]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:lejepa-theorem-ledger` | `2` | `reports/canonical/claim_verdicts.jsonl:$.lines[29]` | `assumption_complexity=0, proof_burden=0, evidence_burden=2, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:observed-debt-sweep` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[30]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:spectral-ablation-hinge` | `6` | `reports/canonical/claim_verdicts.jsonl:$.lines[31]` | `assumption_complexity=2, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=1, revocation_fragility=2` |
| `claim:model-comparison` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[32]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:causal-patch-suite` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[33]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:experiment-stack-cards` | `1` | `reports/canonical/claim_verdicts.jsonl:$.lines[34]` | `assumption_complexity=0, proof_burden=0, evidence_burden=1, backend_coupling=0, witness_exposure=0, revocation_fragility=0` |
| `claim:dimension-mismatch-debt-transfer` | `7` | `reports/canonical/claim_verdicts.jsonl:$.lines[35]` | `assumption_complexity=2, proof_burden=0, evidence_burden=2, backend_coupling=0, witness_exposure=1, revocation_fragility=2` |
| `claim:single-threshold-escape` | `7` | `reports/canonical/claim_verdicts.jsonl:$.lines[36]` | `assumption_complexity=2, proof_burden=0, evidence_burden=2, backend_coupling=0, witness_exposure=1, revocation_fragility=2` |
| `claim:training-choice-observability` | `7` | `reports/canonical/claim_verdicts.jsonl:$.lines[37]` | `assumption_complexity=2, proof_burden=0, evidence_burden=2, backend_coupling=0, witness_exposure=1, revocation_fragility=2` |
