# Canonical Report Index

- Generated at: `2026-06-04T13:39:39+00:00`
- Root: `papers/bedc-quality-lab`

## HG-P core reports

| report | status | json | markdown | scope | cost | not-claimed | positive claim | control |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `mixing-family-sweep` | `pass` | `reports/canonical/mixing-family-sweep.json` | `reports/canonical/mixing-family-sweep.md` | `$.applicability_boundary` | `$.source_artifacts.cost_protocol` | `$.applicability_boundary.not_claimed` | `$.coverage_item` | `$.coverage_item` |
| `anisotropic-ou-sweep` | `pass` | `reports/canonical/anisotropic-ou-sweep.json` | `reports/canonical/anisotropic-ou-sweep.md` | `$.applicability_boundary` | `$.source_artifacts.cost_protocol` | `$.applicability_boundary.not_claimed` | `$.transition_debt_by_grid` | `$.config.arm` |
| `gap-head-on-h` | `pass` | `reports/canonical/gap-head-on-h.json` | `reports/canonical/gap-head-on-h.md` | `$.applicability_boundary` | `$.control_protocol` | `$.applicability_boundary.forbidden_inference_columns` | `$.main_claim_status` | `$.control_protocol` |
| `gap-head-discovery` | `pass` | `reports/canonical/gap-head-discovery.json` | `reports/canonical/gap-head-discovery.md` | `$.boundary_checks` | `$.score_terms` | `$.boundary_checks.forbidden_inference_columns` | `$.final_main_claim_status` | `$.matched_random_control` |
| `gap-head-ablation` | `pass` | `reports/canonical/gap-head-ablation.json` | `reports/canonical/gap-head-ablation.md` | `$.applicability_boundary` | `$.control_protocol` | `$.applicability_boundary.not_claimed` | `$.factor_attribution.learned_head.auroc_delta` | `$.control_protocol` |
| `gap-head-threshold-frontier` | `pass` | `reports/canonical/gap-head-threshold-frontier.json` | `reports/canonical/gap-head-threshold-frontier.md` | `$.applicability_boundary` | `$.source_artifacts` | `$.not_claimed` | `$.main_claim_status` | `$.threshold_summary.control_baseline` |
| `gap-head-transfer-atlas` | `pass` | `reports/canonical/gap_head_transfer_atlas.json` | `reports/canonical/gap_head_transfer_atlas.md` | `$.not_claimed` | `$.source_artifacts.metric_helper` | `$.not_claimed` | `$.multi_surface_d5_o` | `$.config.control_arm` |
| `gap-head-attribution-capsule` | `pass` | `reports/canonical/gap_head_attribution_capsule.json` | `reports/canonical/gap_head_attribution_capsule.md` | `$.scope.not_claimed` | `$.cost_protocol_pointer` | `$.scope.not_claimed` | `$.d5_m` | `$.control_pointer` |
| `certificate-guided-training` | `pass` | `reports/canonical/certificate-guided-training.json` | `reports/canonical/certificate-guided-training.md` | `$.objective.required_rows` | `$.cost_protocol` | `$.not_claimed` | `$.claim_gate` | `$.paired_seed_protocol` |
| `certificate-guided-discovery` | `pass` | `reports/canonical/certificate-guided-discovery.json` | `reports/canonical/certificate-guided-discovery.md` | `$.applicability_boundary` | `$.claim_gate` | `$.not_claimed` | `$.main_claim_status` | `$.matched_random_baseline` |
| `sigreg-training-proxy` | `pass` | `reports/canonical/sigreg-training-proxy.json` | `reports/canonical/sigreg-training-proxy.md` | `$.arm_protocol` | `$.source_artifacts.cost_protocol` | `$.not_claimed` | `$.positive_claim` | `$.full_lejepa_boundary` |

## Auxiliary reports

| report | status | json | markdown | scope | cost | not-claimed | positive claim | control |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `nongaussian-distribution-sweep` | `pass` | `reports/canonical/nongaussian-distribution-sweep.json` | `reports/canonical/nongaussian-distribution-sweep.md` | `$.coverage_item` | `$.source_artifacts.cost_protocol` | `$.not_claimed` | `$.main_claim_status` | `$.negative_result_ledger` |
| `spectral-ablation-hinge` | `pass` | `reports/canonical/spectral-ablation-hinge.json` | `reports/canonical/spectral-ablation-hinge.md` | `$.applicability_boundary` | `$.source_artifacts` | `$.applicability_boundary.not_claimed` | `$.ledger_summary` | `$.negative_control_summary` |

## Quality scorecard

- Status: `pointer-only`
- JSON: `reports/canonical/quality-scorecard.json`
- Markdown: `reports/canonical/quality-scorecard.md`
- Metrics: `CertCov, DebtQ, CriticalDebt, LedgerCompleteness, ClassifierShiftCount, PositiveDiscoveryCount, AuditImprovementCount, NegativeResultCount, ScopeCompleteness, CostProtocolCompleteness, HardeningCoverage, OverclaimRate`

## Discovery map

- Status: `pointer-only`
- JSON: `reports/canonical/discovery_map.json`
- Markdown: `reports/canonical/discovery_map.md`
- Rows: `14`

## Dimension mismatch debt transfer

- Status: `pointer-only`
- JSON: `reports/canonical/dimension-mismatch-debt-transfer.json`
- Markdown: `reports/canonical/dimension-mismatch-debt-transfer.md`
- Transfer status: `pass`
- Base level: `D4`
- Effective level: `DN`
- Terminal verdict: `negative_discovery`

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
- Expected kinds: `8`

## Claim verdicts

- Status: `pointer-only`
- JSONL: `reports/canonical/claim_verdicts.jsonl`
- Rows: `22`

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
- Rows: `13`
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
- D5-O: `ready`
- D5-M: `blocked`
- Mechanism case: `Case 2`

## Gap-head mechanism attribution

- Status: `pointer-only`
- JSON: `reports/gap_head_mechanism_attribution.json`
- Markdown: `reports/gap_head_mechanism_attribution.md`
- Mechanism status: `D5-O retained, mechanism = probe-margin-channel`
- Arms: `22`
- Canonical role: `sidecar_not_in_CANONICAL_REPORTS`

## Release manifest sidecar

- Status: `pointer-only`
- JSON: `reports/release_manifest_sidecar.json`
- Markdown: `reports/release_manifest_sidecar.md`
- Canonical role: `sidecar_not_in_CANONICAL_REPORTS`
- Release bundle status: `ready`
- Tag status: `absent`
- Version: `0.1.0`

## Paper outline

- Status: `pointer-only`
- Core reports: `mixing-family-sweep, anisotropic-ou-sweep, gap-head-on-h, gap-head-discovery, gap-head-ablation, gap-head-threshold-frontier, gap-head-transfer-atlas, gap-head-attribution-capsule, certificate-guided-training, certificate-guided-discovery, sigreg-training-proxy`
- Auxiliary reports: `nongaussian-distribution-sweep, spectral-ablation-hinge`
- Sections: `experiment bench scope, cost protocol, control discipline, negative-result ledger, honest boundary`

## Claims and non-claims

- Status: `pointer-only`

| report | role | positive claim pointer | control pointer | no-control rationale pointer |
| --- | --- | --- | --- | --- |
| `mixing-family-sweep` | `hg_p_core` | `$.coverage_item` | `None` | `$.coverage_item` |
| `anisotropic-ou-sweep` | `hg_p_core` | `$.transition_debt_by_grid` | `None` | `$.config.arm` |
| `gap-head-on-h` | `hg_p_core` | `$.main_claim_status` | `$.control_protocol` | `None` |
| `gap-head-discovery` | `hg_p_core` | `$.final_main_claim_status` | `$.matched_random_control` | `None` |
| `gap-head-ablation` | `hg_p_core` | `$.factor_attribution.learned_head.auroc_delta` | `$.control_protocol` | `None` |
| `gap-head-threshold-frontier` | `hg_p_core` | `$.main_claim_status` | `$.threshold_summary.control_baseline` | `None` |
| `gap-head-transfer-atlas` | `hg_p_core` | `$.multi_surface_d5_o` | `$.config.control_arm` | `None` |
| `gap-head-attribution-capsule` | `hg_p_core` | `$.d5_m` | `$.control_pointer` | `None` |
| `nongaussian-distribution-sweep` | `auxiliary` | `$.main_claim_status` | `None` | `$.negative_result_ledger` |
| `certificate-guided-training` | `hg_p_core` | `$.claim_gate` | `$.paired_seed_protocol` | `None` |
| `certificate-guided-discovery` | `hg_p_core` | `$.main_claim_status` | `$.matched_random_baseline` | `None` |
| `sigreg-training-proxy` | `hg_p_core` | `$.positive_claim` | `None` | `$.full_lejepa_boundary` |
| `spectral-ablation-hinge` | `auxiliary` | `$.ledger_summary` | `$.negative_control_summary` | `None` |

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
