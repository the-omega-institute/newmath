# Canonical Report Index

- Generated at: `2026-06-04T06:25:51.157766+00:00`
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
| `gap-head-attribution-v3` | `pass` | `reports/canonical/gap_head_attribution_v3.json` | `reports/canonical/gap_head_attribution_v3.md` | `$.scope.not_claimed` | `$.cost_protocol_pointer` | `$.scope.not_claimed` | `$.d5_m` | `$.control_pointer` |
| `certificate-guided-training` | `pass` | `reports/canonical/certificate-guided-training.json` | `reports/canonical/certificate-guided-training.md` | `$.objective.required_rows` | `$.cost_protocol` | `$.not_claimed` | `$.claim_gate` | `$.paired_seed_protocol` |
| `certificate-guided-discovery` | `pass` | `reports/canonical/certificate-guided-discovery.json` | `reports/canonical/certificate-guided-discovery.md` | `$.applicability_boundary` | `$.claim_gate` | `$.not_claimed` | `$.main_claim_status` | `$.matched_random_baseline` |

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
- Rows: `12`

## Dimension mismatch debt transfer

- Status: `pointer-only`
- JSON: `reports/canonical/dimension-mismatch-debt-transfer.json`
- Markdown: `reports/canonical/dimension-mismatch-debt-transfer.md`
- Transfer status: `pass`
- Discovery level: `D4`

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
- Rows: `18`

## Negative witness summary

- Status: `pointer-only`
- JSON: `reports/canonical/discovery_negative_witness_summary.json`
- Markdown: `reports/canonical/discovery_negative_witness_summary.md`
- Rows: `12`
- Audit: `pass`

## Formal hardening

- Status: `pointer-only`
- JSON: `reports/canonical/formal_hardening.json`
- Markdown: `reports/canonical/formal_hardening.md`
- Ready: `True`
- Coverage: `4/4`
- Gaps: `0`

## Gap-head attribution capsule

- Status: `pointer-only`
- JSON: `reports/canonical/gap_head_attribution_v3.json`
- Markdown: `reports/canonical/gap_head_attribution_v3.md`
- Run id: `a1-20260604T062534Z`
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

## Paper outline

- Status: `pointer-only`
- Core reports: `mixing-family-sweep, anisotropic-ou-sweep, gap-head-on-h, gap-head-discovery, gap-head-ablation, gap-head-threshold-frontier, gap-head-attribution-v3, certificate-guided-training, certificate-guided-discovery`
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
| `gap-head-attribution-v3` | `hg_p_core` | `$.d5_m` | `$.control_pointer` | `None` |
| `nongaussian-distribution-sweep` | `auxiliary` | `$.main_claim_status` | `None` | `$.negative_result_ledger` |
| `certificate-guided-training` | `hg_p_core` | `$.claim_gate` | `$.paired_seed_protocol` | `None` |
| `certificate-guided-discovery` | `hg_p_core` | `$.main_claim_status` | `$.matched_random_baseline` | `None` |
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
