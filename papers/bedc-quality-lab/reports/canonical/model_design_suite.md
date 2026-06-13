# Model Design Suite

- Generated at: `2026-06-13T08:49:46.900678+00:00`
- Artifact: `bedc-quality-lab:model-design-suite`
- Schema: `bedc-quality-lab:model-design-suite`
- Status: `pass`
- Coverage matrix: `reports/canonical/discovery_map.json:$.coverage_matrix`

## Coverage Rows

| component | owner | discovery | verdict | mechanism | debt | not claimed | negative witness | status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `reports/canonical/ledger-aware-transformer.json:$.artifact_id` | `reports/canonical/ledger-aware-transformer.json:$` | `reports/canonical/discovery-gated-transformer.json:$.hardgate.gates.DGT-HG11` | `reports/canonical/discovery-gated-transformer.json:$.hardgate.status` | `reports/canonical/ledger-aware-transformer.json:$.run_artifacts` | `reports/canonical/discovery-gated-transformer.json:$.component_refs` | `reports/canonical/discovery-gated-transformer.json:$.not_claimed` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[6]` | `pass` |
| `reports/canonical/certificate-gated-attention.json:$.artifact_id` | `reports/canonical/certificate-gated-attention.json:$` | `reports/canonical/discovery-gated-transformer.json:$.hardgate.gates.DGT-HG19` | `reports/canonical/discovery-gated-transformer.json:$.hardgate.status` | `reports/canonical/certificate-gated-attention.json:$.certificate_gate_summary` | `reports/canonical/discovery-gated-transformer.json:$.discovery_map_signal` | `reports/canonical/discovery-gated-transformer.json:$.not_claimed` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[3]` | `pass` |
| `reports/canonical/discovery-regularized-training.json:$.artifact_id` | `reports/canonical/discovery-regularized-training.json:$` | `reports/canonical/discovery-gated-transformer.json:$.hardgate.gates.DGT-HG14` | `reports/canonical/discovery-gated-transformer.json:$.hardgate.status` | `reports/canonical/discovery-regularized-training.json:$.training_mechanism_cert` | `reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary.hardgate` | `reports/canonical/discovery-gated-transformer.json:$.not_claimed` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries` | `pass` |
| `reports/canonical/mechanism-seeking-network.json:$.artifact_id` | `reports/canonical/mechanism-seeking-network.json:$` | `reports/canonical/mechanism-seeking-network.json:$.discovery_map_signal` | `reports/canonical/mechanism-seeking-network.json:$.hardgate.status` | `reports/canonical/mechanism-seeking-network.json:$.mechanism_gate_summary` | `reports/canonical/mechanism-seeking-network.json:$.revocation_rows` | `reports/canonical/mechanism-seeking-network.json:$.not_claimed` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[7]` | `pass` |
| `reports/canonical/discovery-gated-transformer.json:$.artifact_id` | `reports/canonical/discovery-gated-transformer.json:$` | `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.convergence_crossover` | `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.verdict` | `reports/canonical/dgt-neural-ablation.json:$.nabl_hardgates.status` | `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.hardgates` | `reports/canonical/dgt-l1-controls.json:$.l1_step_ladder.not_claimed` | `reports/canonical/dgt-l0-controls.json:$.negative_witness_sweep` | `pass` |

## Hardgates

| gate | status | reason |
| --- | --- | --- |
| `SUITE-HG1` | `pass` | component_id pointers are artifact-qualified and non-empty |
| `SUITE-HG2` | `pass` | canonical_owner_pointer resolves for every row |
| `SUITE-HG3` | `pass` | discovery pointers resolve for every row |
| `SUITE-HG4` | `pass` | verdict and mechanism pointers resolve for every row |
| `SUITE-HG5` | `pass` | row hardgate statuses propagate to the suite status |
