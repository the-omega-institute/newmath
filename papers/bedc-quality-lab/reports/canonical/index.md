# Canonical Report Index

- Generated at: `2026-06-03T05:12:47.442390+00:00`
- Root: `papers/bedc-quality-lab`

## HG-P core reports

| report | status | json | markdown | scope | cost | not-claimed | positive claim | control |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `mixing-family-sweep` | `pass` | `reports/canonical/mixing-family-sweep.json` | `reports/canonical/mixing-family-sweep.md` | `$.applicability_boundary` | `$.source_artifacts.cost_protocol` | `$.applicability_boundary.not_claimed` | `$.coverage_item` | `$.coverage_item` |
| `anisotropic-ou-sweep` | `pass` | `reports/canonical/anisotropic-ou-sweep.json` | `reports/canonical/anisotropic-ou-sweep.md` | `$.applicability_boundary` | `$.source_artifacts.cost_protocol` | `$.applicability_boundary.not_claimed` | `$.transition_debt_by_grid` | `$.config.arm` |
| `gap-head-on-h` | `pass` | `reports/canonical/gap-head-on-h.json` | `reports/canonical/gap-head-on-h.md` | `$.applicability_boundary` | `$.control_protocol` | `$.applicability_boundary.forbidden_inference_columns` | `$.main_claim_status` | `$.control_protocol` |
| `gap-head-discovery` | `pass` | `reports/canonical/gap-head-discovery.json` | `reports/canonical/gap-head-discovery.md` | `$.boundary_checks` | `$.score_terms` | `$.boundary_checks.forbidden_inference_columns` | `$.final_main_claim_status` | `$.matched_random_control` |
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

## Paper outline

- Status: `pointer-only`
- Core reports: `mixing-family-sweep, anisotropic-ou-sweep, gap-head-on-h, gap-head-discovery, certificate-guided-training, certificate-guided-discovery`
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
| `nongaussian-distribution-sweep` | `auxiliary` | `$.main_claim_status` | `None` | `$.negative_result_ledger` |
| `certificate-guided-training` | `hg_p_core` | `$.claim_gate` | `$.paired_seed_protocol` | `None` |
| `certificate-guided-discovery` | `hg_p_core` | `$.main_claim_status` | `$.matched_random_baseline` | `None` |
| `spectral-ablation-hinge` | `auxiliary` | `$.ledger_summary` | `$.negative_control_summary` | `None` |

## Literature ledger pointer

- Status: `not-ready`
- Pointer: `docs/lit/literature_ledger.yaml`

## Honest boundary

- Status: `explicit`
- Claimed: Executable, auditable experiment bench that records negative results.
- Not claimed: Solved model quality.
- EvidenceEnvelope is not NameCert.
- Candidate is not full certification.
- Bound projection is not full proof.
- Hardening is not closure.
