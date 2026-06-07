# Model Mutation Lineage Graph

- Ledger: `reports/canonical/negative_witness_mutation_ledger.json:$.entries`
- Status: `ready`
- Entry count: `8`

| witness kind | target module | source pointer | lineage parent | status |
| --- | --- | --- | --- | --- |
| `score_margin_shortcut` | `residualized_h_path` | `reports/runs/a1-canonical/claim_capsule.json:$.run_local.negative_witness[0]` | `reports/runs/a1-canonical/claim_capsule.json:$.run_local.negative_witness[0]` | `ready` |
| `scale_leakage` | `scale_invariant_norm` | `reports/runs/dimension-mismatch-debt-transfer/controlled-geometry/claim_capsule.json:$.run_local.negative_witness[0]` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[0]` | `ready` |
| `control_positive` | `control_separated_route` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[1]` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[1]` | `ready` |
| `benefit_debt_tradeoff` | `constrained_lagrangian_loss` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[6]` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[2]` | `ready` |
| `single_threshold_escape` | `threshold_frontier_loss` | `runs/single_threshold_escape_witness.json:$.single_threshold_basis[0]` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[3]` | `ready` |
| `forbidden_column` | `inference_audit_layer` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[5]` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[4]` | `ready` |
| `hidden_debt` | `explicit_ledger_head` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[2]` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[5]` | `ready` |
| `mechanism_blocked` | `mechanism_seeking_module` | `reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence` | `reports/canonical/negative_witness_mutation_ledger.json:$.entries[6]` | `ready` |
