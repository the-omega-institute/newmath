# Model Design Suite

- Generated at: `2026-06-07T00:00:00+00:00`
- Artifact: `bedc-quality-lab:model-design-suite`
- Schema: `bedc-quality-lab:model-design-suite`
- Status: `pass`
- Coverage matrix: `reports/canonical/discovery_map.json:$.coverage_matrix`

## Coverage Rows

| component | owner | discovery | verdict | mechanism | debt | not claimed | negative witness | status |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `reports/canonical/model_design_suite.json:$.suite_local_owner_declarations.suite.component_id` | `reports/canonical/model_design_suite.json:$.suite_local_owner_declarations.suite` | `reports/canonical/discovery_map.json:$.coverage_matrix` | `reports/canonical/discovery_map.json:$.level_counts` | `reports/canonical/discovery_gated_transformer.json:$.mechanism_certificate` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries` | `reports/canonical/model_design_suite.json:$.not_claimed` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses` | `pass` |
| `reports/canonical/model_design_suite.json:$.suite_local_owner_declarations.discovery_gated_transformer.component_id` | `reports/canonical/model_design_suite.json:$.suite_local_owner_declarations.discovery_gated_transformer` | `reports/canonical/discovery_gated_transformer.json:$.public_index_pointers` | `reports/canonical/discovery_gated_transformer.json:$.status` | `reports/canonical/discovery_gated_transformer.json:$.mechanism_certificate` | `reports/canonical/discovery_gated_transformer.json:$.downstream_scope` | `reports/canonical/discovery_gated_transformer.json:$.not_claimed` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries` | `pass` |
| `reports/canonical/discovery_gated_transformer.json:$.component_descriptors.backbone` | `reports/canonical/ledger-aware-transformer.json:$` | `reports/canonical/discovery_gated_transformer.json:$.dgt_hardgate_slots.DGT-HG1` | `reports/canonical/discovery_gated_transformer.json:$.dgt_hardgate_slots.overall_state` | `reports/canonical/ledger-aware-transformer.json:$.run_artifacts` | `reports/canonical/discovery_gated_transformer.json:$.dgt_hardgate_slots.DGT-HG5` | `reports/canonical/discovery_gated_transformer.json:$.not_claimed` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[6]` | `pass` |
| `reports/canonical/discovery_gated_transformer.json:$.component_descriptors.certificate_gated_attention` | `reports/canonical/certificate-gated-attention.json:$` | `reports/canonical/discovery_gated_transformer.json:$.dgt_hardgate_slots.DGT-HG8` | `reports/canonical/discovery_gated_transformer.json:$.dgt_hardgate_slots.overall_state` | `reports/canonical/certificate-gated-attention.json:$.certificate_gate_summary` | `reports/canonical/discovery_gated_transformer.json:$.mechanism_certificate.mechanism_hardgate_slots.DGT-MECH-HG3` | `reports/canonical/discovery_gated_transformer.json:$.not_claimed` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[3]` | `pass` |
| `reports/canonical/discovery_gated_transformer.json:$.component_descriptors.discovery_regularized_training` | `reports/canonical/discovery-regularized-training.json:$` | `reports/canonical/discovery_gated_transformer.json:$.dgt_hardgate_slots.DGT-HG9` | `reports/canonical/discovery_gated_transformer.json:$.dgt_hardgate_slots.overall_state` | `reports/canonical/discovery-regularized-training.json:$.torch_training_evidence` | `reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary.hardgate` | `reports/canonical/discovery_gated_transformer.json:$.not_claimed` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries` | `pass` |
| `reports/canonical/discovery_gated_transformer.json:$.component_descriptors.gap_ledger_route_mechanism_scope_heads` | `reports/canonical/gap_head_attribution_capsule.json:$` | `reports/canonical/discovery_gated_transformer.json:$.dgt_hardgate_slots.DGT-HG10` | `reports/canonical/discovery_gated_transformer.json:$.mechanism_certificate.overall_state` | `reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence` | `reports/canonical/gap_head_attribution_capsule.json:$.ledger_debt` | `reports/canonical/discovery_gated_transformer.json:$.not_claimed` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[7]` | `pass` |

## Hardgates

| gate | status | reason |
| --- | --- | --- |
| `SUITE-HG1` | `pass` | component_id pointers are artifact-qualified and non-empty |
| `SUITE-HG2` | `pass` | canonical_owner_pointer resolves for every row |
| `SUITE-HG3` | `pass` | discovery pointers resolve for every row |
| `SUITE-HG4` | `pass` | verdict and mechanism pointers resolve for every row |
| `SUITE-HG5` | `pass` | row hardgate statuses propagate to the suite status |
