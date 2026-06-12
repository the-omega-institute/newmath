# Canonical Report Index

- Generated at: `2026-06-11T08:40:12.594518+00:00`
- Root: `papers/bedc-quality-lab`

## HG-P core reports

| report | status | hardgate | CV | missing hardgate cells | json | markdown | fingerprint | scope | cost | not-claimed | positive claim | control |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |

## Auxiliary reports

| report | status | hardgate | CV | missing hardgate cells | json | markdown | fingerprint | scope | cost | not-claimed | positive claim | control |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `dgt-base-undertraining-audit` | `pass` | `not-applicable` | `not-applicable` | `` | `reports/canonical/dgt-base-undertraining-audit.json` | `reports/canonical/dgt-base-undertraining-audit.md` | `reports/canonical/dgt-base-undertraining-audit.fingerprint.json` | `$.base_undertraining_audit.not_claimed` | `$.base_undertraining_audit.source_contract` | `$.base_undertraining_audit.not_claimed` | `$.base_undertraining_audit.verdict` | `$.base_undertraining_audit.comparison_rows` |

## Dashboard

- Status: `pointer-only`
- Artifact pointer: `bedc-quality-lab:dashboard`
- Canonical role: `navigation_view_not_fact_source`

## Quality scorecard

- Status: `pointer-only`
- JSON: `reports/canonical/quality-scorecard.json`
- Markdown: `reports/canonical/quality-scorecard.md`
- Metrics: `CertCov, DebtQ, CriticalDebt, LedgerCompleteness, ClassifierShiftCount, PositiveDiscoveryCount, AuditImprovementCount, NegativeResultCount, ScopeCompleteness, CostProtocolCompleteness, HardeningCoverage, OverclaimRate`

## Discovery map

- Status: `pointer-only`
- JSON: `reports/canonical/discovery_map.json`
- Markdown: `reports/canonical/discovery_map.md`
- Coverage matrix: `reports/canonical/discovery_map.json:$.coverage_matrix`
- Rows: `35`

## Experiment proposals

- Status: `pointer-only`
- JSON: `reports/canonical/experiment_proposals.json`
- Markdown: `reports/canonical/experiment_proposals.md`
- Rows: `7`
- Proposal rows: `reports/canonical/experiment_proposals.json:$.rows`
- Source artifacts: `reports/canonical/experiment_proposals.json:$.source_artifacts`

## Observed debt axis projection

- Status: `pointer-only`
- Rows: `8`
- Classifications: `observed-debt, ledger-risk-only`

| axis | classification | source | evidence | hardgate |
| --- | --- | --- | --- | --- |
| `latent_distribution` | `ledger-risk-only` | `reports/canonical/nongaussian-distribution-sweep.json` | `$.main_claim_status` | `$.claim_gate` |
| `anisotropy` | `ledger-risk-only` | `reports/canonical/anisotropic-ou-sweep.json` | `$.transition_debt_by_grid.rho_axes_0p95_0p3` | `None` |
| `dimension_mismatch` | `observed-debt` | `reports/canonical/dimension-mismatch-debt-transfer.json` | `$.dimension_mismatch_debt_transfer.status` | `$.hardgate_evidence` |
| `sample_count` | `observed-debt` | `reports/canonical/gap-head-observed-debt-transfer.json` | `$.gap_head_on_h_observed_debt_transfer.status` | `$.hardgate_evidence` |
| `optimizer` | `ledger-risk-only` | `runs/training_choice_observability.json` | `$.training_choice_observability.ledger_risk_only_arm_count` | `$.training_choice_observability.arms[0].hardgates` |
| `mixing` | `ledger-risk-only` | `reports/canonical/mixing-family-sweep.json` | `$.coverage_item` | `None` |
| `compute` | `ledger-risk-only` | `runs/training_choice_observability.json` | `$.source_artifacts.gap_head_metric_helper` | `None` |
| `capacity` | `ledger-risk-only` | `reports/canonical/discovery_gate_escape_registry.json` | `$.capacity` | `None` |

## Dimension mismatch debt transfer

- Status: `pointer-only`
- JSON: `reports/canonical/dimension-mismatch-debt-transfer.json`
- Markdown: `reports/canonical/dimension-mismatch-debt-transfer.md`
- Claim pointer: `reports/canonical/dimension-mismatch-debt-transfer.json:$.dimension_mismatch_debt_transfer`
- Claim present: `True`

## Dimension mismatch transfer robustness

- Status: `pass`
- JSON: `reports/canonical/dimension-mismatch-transfer-robustness.json`
- Markdown: `reports/canonical/dimension-mismatch-transfer-robustness.md`
- Audit status: `pass`

## Quality baseline pointers

- Baseline source: `docs/bedc_quality_lab_alpha_milestone.md`
- Canonical artifacts: `papers/bedc-quality-lab/reports/canonical/`
- Discovery map: `reports/canonical/discovery_map.json:$.rows[*].discovery_level`
- Claim verdicts: `reports/canonical/claim_verdicts.jsonl`
- Claim capsule: `reports/canonical/claim_capsule.json`
- Negative witnesses: `reports/canonical/discovery_negative_witnesses.json`
- Scorecard: `reports/canonical/quality-scorecard.json:$.rows`
- Claims boundary: `docs/claims_and_nonclaims.md`
- Manifest: `docs/artifact_manifest.md`

## Negative witnesses

- Status: `pointer-only`
- JSON: `reports/canonical/discovery_negative_witnesses.json`
- Expected kinds: `9`

## Negative discovery reports

- Status: `pointer-only`
- JSON: `reports/canonical/negative_discovery_reports.json`
- Markdown: `reports/canonical/negative_discovery_reports.md`
- Rows: `7`
- Audit: `pass`

## Negative witness mutation ledger

- Status: `ready`
- JSON: `reports/canonical/negative_witness_mutation_ledger.json`
- Graph: `reports/canonical/model_mutation_lineage_graph.md`
- DGT report: `reports/canonical/dgt_mutation_report.json`
- Canonical role: `sidecar_not_in_CANONICAL_REPORTS`
- Entries: `8`
- Entries pointer: `reports/canonical/negative_witness_mutation_ledger.json:$.entries`

## New model hardgates

- Status: `pointer-only`
- JSON: `reports/canonical/new_model_hardgates.json`
- Markdown: `reports/canonical/new_model_hardgates.md`
- Schema: `bedc-quality-lab:new-model-hardgates`
- Canonical role: `sidecar_not_in_CANONICAL_REPORTS`
- Gate ids pointer: `reports/canonical/new_model_hardgates.json:$.gate_ids`
- Gates pointer: `reports/canonical/new_model_hardgates.json:$.gates`
- Gate count: `20`

## Discovery-Regularized Training Quality Boundary

- Status: `present-but-fail-closed`
- JSON: `reports/canonical/discovery-regularized-training.json`
- Markdown: `reports/canonical/discovery-regularized-training.md`
- Owner: `reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary`
- Hardgate: `reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary.hardgate`
- Arm comparisons: `reports/canonical/discovery-regularized-training.json:$.quality_promotion_boundary.arm_comparisons`

## Discovery-Gated Transformer

- Status: `pass`
- JSON: `reports/canonical/discovery-gated-transformer.json`
- Markdown: `reports/canonical/discovery-gated-transformer.md`
- Schema: `bedc-quality-lab:discovery-gated-transformer`
- Model id: `reports/canonical/discovery-gated-transformer.json:$.model_id`
- Architecture: `reports/canonical/discovery-gated-transformer.json:$.architecture_spec`
- Components: `reports/canonical/discovery-gated-transformer.json:$.component_refs`
- Hardgate: `reports/canonical/discovery-gated-transformer.json:$.hardgate`
- Tool route evidence: `reports/canonical/discovery-gated-transformer.json:$.tool_route_evidence`
- Tool route hardgate: `reports/canonical/discovery-gated-transformer.json:$.tool_route_evidence.hardgate`
- Family definition: `reports/canonical/discovery-gated-transformer.json:$.family_definition`
- Family definition hardgate: `reports/canonical/discovery-gated-transformer.json:$.family_definition.hardgate`
- Model family claim status: `reports/canonical/discovery-gated-transformer.json:$.family_definition.model_family_claim_status`
- Robustness: `reports/canonical/discovery-gated-transformer.json:$.operational_robustness`
- Robustness readiness: `reports/canonical/discovery-gated-transformer.json:$.operational_robustness.readiness`
- Robustness hardgate: `reports/canonical/discovery-gated-transformer.json:$.operational_robustness.hardgate`
- D5-M projection: `reports/canonical/discovery-gated-transformer.json:$.d5_m_projection`
- D5-M discovery level: `reports/canonical/discovery-gated-transformer.json:$.d5_m_projection.discovery_level`
- Scaling ladder: `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder`
- Scaling ladder discovery level: `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.discovery_level`
- Scaling ladder status: `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.status`
- L1 control projection: `reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection`
- L1 review status: `reports/canonical/dgt-l1-controls.json:$.review_status`
- Not claimed: `reports/canonical/discovery-gated-transformer.json:$.not_claimed`
- Discovery map signal: `reports/canonical/discovery-gated-transformer.json:$.discovery_map_signal`
- Claim capsule: `reports/canonical/discovery-gated-transformer.json:$.claim_capsule_ref`
- Evidence envelope: `reports/canonical/discovery-gated-transformer.json:$.evidence_envelope_ref`
- Mechanism NameCert: `reports/canonical/discovery-gated-transformer.json:$.mechanism_namecert_ref`
- Jet certificate: `reports/canonical/discovery-gated-transformer.json:$.jet_certificate_ref`

## Model Design Suite

- Status: `pass`
- JSON: `reports/canonical/model_design_suite.json`
- Markdown: `reports/canonical/model_design_suite.md`
- Schema: `bedc-quality-lab:model-design-suite`
- Owner: `reports/canonical/model_design_suite.json:$`
- Rows: `reports/canonical/model_design_suite.json:$.rows`
- Hardgates: `reports/canonical/model_design_suite.json:$.hardgates`
- Coverage matrix: `reports/canonical/discovery_map.json:$.coverage_matrix`

## Model Comparison

- Status: `pointer-only`
- Sidecar status: `ready`
- JSON: `reports/canonical/model-comparison.json`
- Markdown: `reports/canonical/model-comparison.md`
- Schema: `bedc-quality-lab:model-comparison`
- Models: `reports/canonical/model-comparison.json:$.models`
- Hardgates: `reports/canonical/model-comparison.json:$.hardgates`
- Ranking key: `reports/canonical/model-comparison.json:$.ranking_key`
- Source reports: `reports/canonical/model-comparison.json:$.source_reports`

## Issue 1012 sidecars

- Status: `pointer-only`
- Canonical role: `sidecar_not_in_CANONICAL_REPORTS`

| sidecar | owner | artifact | pointer |
| --- | --- | --- | --- |
| `lejepa-derivative-bridge` | `lejepa-theorem-ledger` | `reports/canonical/lejepa_derivative_bridge.json` | `reports/canonical/lejepa_theorem_ledger.json:$.hermite_degree_boundary` |
| `hermite-degree-vs-behavioral-derivative` | `lejepa-theorem-ledger` | `reports/canonical/hermite_degree_vs_behavioral_derivative.md` | `reports/canonical/lejepa_theorem_ledger.json:$.hermite_degree_boundary` |
| `spectral-jet-report` | `spectral-ablation-hinge` | `reports/canonical/spectral_jet_report.json` | `reports/canonical/spectral-ablation-hinge.json:$.spectral_jet` |

## Claim verdicts

- Status: `pointer-only`
- JSONL: `reports/canonical/claim_verdicts.jsonl`
- Rows: `44`

## Claim complexity

- Status: `fail`
- JSON: `reports/canonical/claim_complexity.json`
- Markdown: `reports/canonical/claim_complexity.md`
- Canonical role: `artifact_only_evidence`
- Rows: `34`
- Row pointer: `reports/canonical/claim_complexity.json:$.rows`
- Verdict refs: `reports/canonical/claim_complexity.json:$.rows[*].pointer_only_verdict_ref`
- Terminal verdict owner: `bedc-quality-lab:claim-verdicts`

## Claim graph

- Status: `pointer-only`
- JSON: `reports/canonical/claim_graph.json`
- Markdown: `reports/canonical/claim_graph.md`
- Canonical role: `sidecar_not_in_CANONICAL_REPORTS`
- Nodes: `128`

## Claim artifact consistency

- Status: `pass`
- JSON: `reports/canonical/claim-artifact-consistency.json`
- Markdown: `reports/canonical/claim-artifact-consistency.md`
- Claim: `claim:discovery-gated-transformer`
- Gates: `reports/canonical/claim-artifact-consistency.json:$.gates`

## Claim capsule

- Status: `pointer-only`
- JSON: `reports/canonical/claim_capsule.json`
- Schema: `bedc.quality.claim_capsule`
- Effective level: `DN`
- Terminal verdict: `negative_discovery`

## Negative witness summary

- Status: `pointer-only`
- JSON: `reports/canonical/discovery_negative_witness_summary.json`
- Markdown: `reports/canonical/discovery_negative_witness_summary.md`
- Rows: `16`
- Audit: `pass`

## Formal hardening

- Status: `pointer-only`
- JSON: `reports/canonical/formal_hardening.json`
- Markdown: `reports/canonical/formal_hardening.md`
- Ready: `True`
- Coverage: `4/4`
- Gaps: `0`

## Gap-head transfer atlas

- Status: `pointer-only`
- JSON: `reports/canonical/gap_head_transfer_atlas.json`
- Markdown: `reports/canonical/gap_head_transfer_atlas.md`
- Decision pointer: `$.multi_surface_d5_o`
- Boundary ledger pointer: `$.boundary_ledger`
- Claim capsule pointer: `$.config.claim_capsule_artifact`

## Gap-head attribution capsule

- Status: `pointer-only`
- JSON: `reports/canonical/gap_head_attribution_capsule.json`
- Markdown: `reports/canonical/gap_head_attribution_capsule.md`
- Run id: `a1-canonical`
- D5-O: `blocked`
- D5-M: `blocked`
- Mechanism case: `unresolved`

## Release manifest sidecar

- Status: `pointer-only`
- JSON: `reports/release_manifest_sidecar.json`
- Markdown: `reports/release_manifest_sidecar.md`
- Canonical role: `sidecar_not_in_CANONICAL_REPORTS`
- Release bundle status: `ready`
- Tag status: `absent`
- Version: `0.0.1`

## Release readiness

- Status: `pointer-only`
- Canonical role: `index_projection_not_fact_source`
- Freshness hardgate: `scripts/run_canonical_reports.py --verify-fingerprints`
- Sources: `8`
- Not claimed: `This section does not copy scorecard, discovery, formal, claim, or release facts; read the listed owner pointers and use --verify-fingerprints for stale-hash failure.`

| source | artifact | pointer | owner |
| --- | --- | --- | --- |
| `Canonical index` | `reports/canonical/index.json` | `$` | `reports/canonical/index.json:$` |
| `Quality scorecard` | `reports/canonical/quality-scorecard.json` | `$.rows` | `reports/canonical/quality-scorecard.json:$.rows` |
| `Discovery map` | `reports/canonical/discovery_map.json` | `$.coverage_matrix` | `reports/canonical/discovery_map.json:$.coverage_matrix` |
| `Claim graph` | `reports/canonical/claim_graph.json` | `$` | `reports/canonical/claim_graph.json:$` |
| `Claim verdicts` | `reports/canonical/claim_verdicts.jsonl` | `$` | `reports/canonical/claim_verdicts.jsonl:$` |
| `Negative witnesses` | `reports/canonical/discovery_negative_witnesses.json` | `$` | `reports/canonical/discovery_negative_witnesses.json:$` |
| `Formal hardening` | `reports/canonical/formal_hardening.json` | `$` | `reports/canonical/formal_hardening.json:$` |
| `Release manifest sidecar` | `reports/release_manifest_sidecar.json` | `$.release_bundle_status` | `reports/release_manifest_sidecar.json:$.release_bundle_status` |

## Toy latent planning BEDC

- Status: `pointer-only`
- JSON: `reports/toy_latent_planning_bedc/toy_latent_planning_bedc.json`
- Canonical role: `sidecar_not_in_CANONICAL_REPORTS`
- Owner package: `experiments/toy_latent_planning_bedc`
- Hardgate status pointer: `reports/toy_latent_planning_bedc/claim_capsule.json:$.u_hardgates.status`

## Release NameCert candidate

- Status: `pointer-only`
- JSON: `reports/release_namecert_candidate.json`
- Markdown: `reports/release_namecert_candidate.md`
- Owner artifact: `bedc-quality-lab:release-manifest-sidecar`
- Candidate status: `ready-candidate`
- Revoke pointer: `$.ledger_policy.revoke_if`

## Toy safety boundary

- Status: `pointer-only`
- JSON: `reports/canonical/toy_safety_boundary.json`
- Markdown: `reports/canonical/toy_safety_boundary.md`
- Claim capsule: `experiments/toy_safety_boundary/reports/runs/toy_safety_boundary/claim_capsule.json:$`
- Hardgates: `experiments/toy_safety_boundary/reports/runs/toy_safety_boundary/claim_capsule.json:$.hardgates`

## Boundary-Causal-Derivative

- Status: `no_rows_yet`
- Schema: `reports/canonical/boundary_causal_derivative_schema.json`
- Spec: `reports/canonical/boundary_causal_derivative_spec.md`
- Ledger: `reports/canonical/derivative_order_ledger.json`
- Matrix: `reports/canonical/jet_coverage_matrix.json`
- Canonical role: `sidecar_not_in_CANONICAL_REPORTS`
- Hardgates: `reports/canonical/boundary_causal_derivative_schema.json:$.hardgates`

## Irreducibility Report

- Status: `pass`
- JSON: `reports/canonical/irreducibility_report.json`
- Markdown: `reports/canonical/order_residual_analysis.md`
- CMI table: `reports/canonical/conditional_information_table.json`
- Hardgate: `reports/canonical/irreducibility_report.json:$.hardgate`
- Positive claim: `reports/canonical/irreducibility_report.json:$.positive_claim`
- CMI rows: `reports/canonical/conditional_information_table.json:$.rows`

## Paper outline

- Status: `pointer-only`
- Core reports: ``
- Auxiliary reports: `dgt-base-undertraining-audit`
- Sections: `experiment bench scope, cost protocol, control discipline, negative-result ledger, honest boundary`

## Claims and non-claims

- Status: `pointer-only`

| report | role | positive claim pointer | control pointer | no-control rationale pointer |
| --- | --- | --- | --- | --- |
| `dgt-base-undertraining-audit` | `auxiliary` | `$.base_undertraining_audit.verdict` | `$.base_undertraining_audit.comparison_rows` | `None` |

## Literature ledger pointer

- Status: `ready`
- Pointer: `docs/lit/literature_ledger.yaml`

## Honest boundary

- Status: `explicit`
- Claimed: Executable, auditable experiment bench that records negative results.
- Not claimed: Solved model quality.
- EvidenceEnvelope is not NameCert.
- Candidate is not full certification.
- Bound projection is not full proof.
- Hardening is not closure.
