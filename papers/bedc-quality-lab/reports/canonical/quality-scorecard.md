# Quality Scorecard

- Generated at: `2026-06-04T15:16:56.178829+00:00`
- Artifact: `bedc-quality-lab:quality-scorecard`
- Producer: `scripts/run_canonical_reports.py`

## Quality baseline pointers

- Baseline source: `docs/bedc_quality_lab_alpha_milestone.md`
- Discovery levels: `reports/canonical/discovery_map.json:$.rows[*].discovery_level`
- Claims boundary: `docs/claims_and_nonclaims.md`
- Manifest: `docs/artifact_manifest.md`
- Surface: metric rows with source pointers only

## Metric rows

| metric | status | value | source | dependency |
| --- | --- | --- | --- | --- |
| `CertCov` | `ready` | `1.0` | `reports/canonical/mixing-family-sweep.json:$.coverage_item` | `` |
| `DebtQ` | `ready` | `0.0` | `reports/canonical/mixing-family-sweep.json:$.coverage_item.debt_item.score` | `` |
| `CriticalDebt` | `ready` | `0.3` | `reports/canonical/gap-head-discovery.json:$.debt_terms` | `` |
| `LedgerCompleteness` | `ready` | `1.0` | `reports/canonical/gap-head-discovery.json:$.classifier_state` | `` |
| `ClassifierShiftCount` | `ready` | `30` | `reports/canonical/gap-head-discovery.json:$.surface_delta_count` | `` |
| `PositiveDiscoveryCount` | `ready` | `1` | `reports/canonical/gap-head-discovery.json:$.positive_discovery, reports/canonical/certificate-guided-discovery.json:$.positive_discovery` | `` |
| `AuditImprovementCount` | `ready` | `1` | `reports/canonical/certificate-guided-training.json:$.claim_gate.audit_improvement_tradeoff` | `` |
| `NegativeResultCount` | `ready` | `10` | `reports/canonical/mixing-family-sweep.json:$.negative_result_summary.cells, reports/canonical/anisotropic-ou-sweep.json:$.negative_result_summary.cells, reports/canonical/nongaussian-distribution-sweep.json:$.negative_result_ledger` | `` |
| `ScopeCompleteness` | `ready` | `1.0` | `reports/canonical/mixing-family-sweep.json:$.applicability_boundary, reports/canonical/anisotropic-ou-sweep.json:$.applicability_boundary, reports/canonical/gap-head-on-h.json:$.applicability_boundary, reports/canonical/gap-head-discovery.json:$.boundary_checks, reports/canonical/gap-head-ablation.json:$.applicability_boundary, reports/canonical/gap-head-threshold-frontier.json:$.applicability_boundary, reports/canonical/gap_head_transfer_atlas.json:$.not_claimed, reports/canonical/gap_head_attribution_capsule.json:$.scope.not_claimed, reports/canonical/nongaussian-distribution-sweep.json:$.coverage_item, reports/canonical/certificate-guided-training.json:$.objective.required_rows, reports/canonical/certificate-guided-discovery.json:$.applicability_boundary, reports/canonical/sigreg-training-proxy.json:$.arm_protocol, reports/canonical/spectral-ablation-hinge.json:$.applicability_boundary` | `` |
| `CostProtocolCompleteness` | `ready` | `1.0` | `reports/canonical/mixing-family-sweep.json:$.source_artifacts.cost_protocol, reports/canonical/anisotropic-ou-sweep.json:$.source_artifacts.cost_protocol, reports/canonical/gap-head-on-h.json:$.control_protocol, reports/canonical/gap-head-discovery.json:$.score_terms, reports/canonical/gap-head-ablation.json:$.control_protocol, reports/canonical/gap-head-threshold-frontier.json:$.source_artifacts, reports/canonical/gap_head_transfer_atlas.json:$.source_artifacts.metric_helper, reports/canonical/gap_head_attribution_capsule.json:$.cost_protocol_pointer, reports/canonical/nongaussian-distribution-sweep.json:$.source_artifacts.cost_protocol, reports/canonical/certificate-guided-training.json:$.cost_protocol, reports/canonical/certificate-guided-discovery.json:$.claim_gate, reports/canonical/sigreg-training-proxy.json:$.source_artifacts.cost_protocol, reports/canonical/spectral-ablation-hinge.json:$.source_artifacts` | `` |
| `HardeningCoverage` | `ready` | `1.0` | `reports/canonical/formal_hardening.json:$.coverage` | `` |
| `OverclaimRate` | `ready` | `0.0` | `reports/canonical/certificate-guided-discovery.json:$.audit_decision.overclaim_rate` | `` |
