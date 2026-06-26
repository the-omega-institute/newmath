# 最小不可约因果导数层级

- Generated at: `2026-06-15T19:37:00.997010+00:00`
- Artifact: `bedc-quality-lab:minimal-irreducible-causal-derivative-mainline`
- Role: `runner_local_pointer_only_read_model`
- Candidate status: `admissible-pointer-present`

## Source pointers

| id | status | owner pointer |
| --- | --- | --- |
| `dgt-claim-capsule` | `present` | `reports/runs/discovery-gated-transformer/claim_capsule.json:$` |
| `dgt-evidence-envelope` | `present` | `reports/runs/discovery-gated-transformer/evidence_envelope.json:$` |
| `dgt-mainline` | `present` | `reports/canonical/discovery-gated-transformer.json:$.hardgate` |
| `derivative-order-ledger` | `present` | `reports/canonical/derivative_order_ledger.json:$.entries` |
| `boundary-causal-derivative-schema` | `present` | `reports/canonical/boundary_causal_derivative_schema.json:$` |
| `causal-patch-suite` | `present` | `reports/canonical/causal_patch_suite.json:$.hardgates` |
| `irreducibility-report` | `present` | `reports/canonical/irreducibility_report.json:$.hardgate` |
| `negative-witness-summary` | `present` | `reports/canonical/discovery_negative_witness_summary.json:$.rows` |
| `dgt-l0-controls` | `present` | `reports/canonical/dgt-l0-controls.json:$.l0_toy_projection` |
| `dgt-l1-controls` | `present` | `reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection` |
| `dgt-neural-ablation` | `present` | `reports/canonical/dgt-neural-ablation.json:$.nabl_hardgates` |
| `dgt-null-decomposition` | `present` | `reports/canonical/dgt-ablation-null-decomposition.json:$.hardgates` |
| `dgt-component-redundancy` | `present` | `reports/canonical/dgt-component-redundancy-audit.json:$.component_redundancy_audit` |
| `dgt-base-undertraining` | `present` | `reports/canonical/dgt-base-undertraining-audit.json:$.base_undertraining_audit` |
| `model-comparison` | `present` | `reports/canonical/model-comparison.json:$.comparisons` |
| `mechanism-dna` | `present` | `reports/canonical/mechanism_dna.json:$.rows` |
| `new-model-hardgates` | `present` | `reports/canonical/new_model_hardgates.json:$.gates` |
| `claim-graph` | `present` | `reports/canonical/claim_graph.json:$.nodes` |

## negative results

- Status: `pointer-only`
- Summary: `reports/canonical/discovery_negative_witness_summary.json:$.rows`

## not claimed

- This read model does not own terminal claim decisions.
- This read model stores only artifact-qualified pointers, never duplicated source payloads.
- This read model does not create, close, edit, or track GitHub issues.
- A-O route intent without checked-in route bodies is not package-level reuse evidence.

## child artifacts

| id | pointer |
| --- | --- |
| `scorecard-contract` | `reports/canonical/minimal_irreducible_causal_derivative_mainline.json:$` |
| `negative-results` | `reports/canonical/minimal_irreducible_causal_derivative_mainline.json:$.negative_results` |
| `not-claimed` | `reports/canonical/minimal_irreducible_causal_derivative_mainline.json:$.not_claimed` |
