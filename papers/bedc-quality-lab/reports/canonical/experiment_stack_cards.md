# Experiment Stack Cards

- Generated at: `2026-06-13T12:52:34.119917+00:00`
- Artifact: `bedc-quality-lab:experiment-stack-cards`
- Status: `blocked`
- Cards: `14`
- Claim-first gate: `reports/canonical/experiment_stack_cards.json:$.claim_first_gate`

## Cards

| card | status | owner issue | owner artifact | source | summary | demotion | hardgates |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `claim-card` | `pass` | `1207` | `reports/runs/discovery-gated-transformer/claim_capsule.json` | `reports/runs/discovery-gated-transformer/claim_capsule.json:$.owner_ref` | `reports/runs/discovery-gated-transformer/claim_capsule.json:$.claim_scope` | `reports/canonical/discovery-gated-transformer.json:$.not_claimed` | `STACK-HG1:pass, STACK-HG2:pass` |
| `task-target-card` | `blocked` | `1207` | `reports/canonical/discovery-gated-transformer.json` | `reports/canonical/discovery-gated-transformer.json:$.d4_projection.matched_control` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.source_projection` | `reports/canonical/discovery-gated-transformer.json:$.scaling_ladder.boundary_ledger` | `STACK-HG1:pass, STACK-HG2:fail` |
| `data-card` | `blocked` | `1201` | `reports/canonical/index.json` | `reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer` | `reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.evidence_type` | `reports/canonical/index.json:$.evidence_provenance.discovery_rows_by_report.discovery-gated-transformer.not_claimed` | `STACK-HG1:pass, STACK-HG2:fail` |
| `feature-access-card` | `pass` | `1209` | `reports/canonical/dgt-l1-controls.json` | `reports/canonical/dgt-l1-controls.json:$.training_arms` | `reports/canonical/dgt-l1-controls.json:$.review_status` | `reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection` | `STACK-HG1:pass, STACK-HG2:pass` |
| `baseline-validity-card` | `blocked` | `1207` | `reports/canonical/dgt-l1-boundary-report.json` | `reports/canonical/dgt-l1-boundary-report.json:$.base_bayes_ceiling` | `reports/canonical/dgt-l1-boundary-report.json:$.feature_reachability` | `reports/canonical/dgt-l1-boundary-report.json:$.claim_promotion_exclusion` | `STACK-HG1:pass, STACK-HG2:fail` |
| `ood-solvability-card` | `blocked` | `1207` | `reports/canonical/dgt-l1-boundary-report.json` | `reports/canonical/dgt-l1-boundary-report.json:$.ood_solvability` | `reports/canonical/dgt-l1-boundary-report.json:$.feature_reachability` | `reports/canonical/dgt-l1-boundary-report.json:$.not_claimed` | `STACK-HG1:pass, STACK-HG2:fail` |
| `metric-provenance-card` | `blocked` | `1201` | `reports/canonical/index.json` | `reports/canonical/index.json:$.evidence_provenance.metric_rows[30]` | `reports/canonical/index.json:$.evidence_provenance.metric_rows[30].source_type` | `reports/canonical/index.json:$.evidence_provenance.metric_rows[30].not_claimed` | `STACK-HG1:pass, STACK-HG2:fail` |
| `training-authenticity-card` | `blocked` | `1201` | `reports/canonical/index.json` | `reports/canonical/index.json:$.evidence_provenance.producer_audits[30]` | `reports/canonical/index.json:$.evidence_provenance.producer_audits[30].training_evidence_status` | `reports/canonical/index.json:$.evidence_provenance.producer_audits[30].not_claimed` | `STACK-HG1:pass, STACK-HG2:fail` |
| `statistical-evidence-card` | `blocked` | `1201` | `reports/canonical/index.json` | `reports/canonical/index.json:$.evidence_provenance.metric_rows[30]` | `reports/canonical/index.json:$.evidence_provenance.metric_rows[30].allowed_for_empirical_claim, reports/canonical/index.json:$.evidence_provenance.metric_rows[30].source_type` | `reports/canonical/index.json:$.evidence_provenance.metric_rows[30].not_claimed` | `STACK-HG1:pass, STACK-HG2:fail` |
| `ablation-causal-evidence-card` | `blocked` | `1207` | `reports/canonical/dgt-neural-ablation.json` | `reports/canonical/dgt-neural-ablation.json:$.boundary_ledger` | `reports/canonical/dgt-neural-ablation.json:$.nabl_hardgates.status` | `reports/canonical/dgt-neural-ablation.json:$.not_claimed` | `STACK-HG1:pass, STACK-HG2:fail` |
| `artifact-reproducibility-card` | `pass` | `1213` | `reports/release_manifest_sidecar.json` | `reports/release_manifest_sidecar.json:$.required_pointers` | `reports/release_manifest_sidecar.json:$.release_bundle_status` | `reports/release_manifest_sidecar.json:$.revoke_if` | `STACK-HG1:pass, STACK-HG2:pass` |
| `model-card` | `pass` | `1220` | `reports/canonical/dgt-model-card.json` | `reports/canonical/dgt-model-card.json:$.intended_use` | `reports/canonical/dgt-model-card.json:$.card_hardgates.status` | `reports/canonical/dgt-model-card.json:$.not_claimed` | `STACK-HG1:pass, STACK-HG2:pass` |
| `risk-scope-review-card` | `blocked` | `1207` | `reports/canonical/dgt-l1-boundary-report.json` | `reports/canonical/dgt-l1-boundary-report.json:$.claim_promotion_exclusion` | `reports/canonical/dgt-l1-boundary-report.json:$.boundary_decision` | `reports/canonical/dgt-l1-boundary-report.json:$.not_claimed` | `STACK-HG1:pass, STACK-HG2:fail` |
| `release-readiness-board` | `blocked` | `1213` | `reports/canonical/reproduction-package.json` | `reports/canonical/reproduction-package.json:$.reproduction_targets` | `reports/canonical/reproduction-package.json:$.hardgates` | `reports/canonical/reproduction-package.json:$.hardgates.REPRO-HG5` | `STACK-HG1:pass, STACK-HG2:fail` |

## Standard Alignment

| standard | external pointer | local card pointers |
| --- | --- | --- |
| `neurips-checklist` | `https://neurips.cc/public/guides/PaperChecklist` | `reports/canonical/experiment_stack_cards.json:$.cards[0]`, `reports/canonical/experiment_stack_cards.json:$.cards[2]`, `reports/canonical/experiment_stack_cards.json:$.cards[8]`, `reports/canonical/experiment_stack_cards.json:$.cards[12]` |
| `papers-with-code-code-completeness` | `https://paperswithcode.com/about` | `reports/canonical/experiment_stack_cards.json:$.cards[10]`, `reports/canonical/experiment_stack_cards.json:$.cards[7]` |
| `acm-artifact-badging` | `https://www.acm.org/publications/policies/artifact-review-badging` | `reports/canonical/experiment_stack_cards.json:$.cards[10]`, `reports/canonical/experiment_stack_cards.json:$.cards[13]` |
| `model-cards` | `https://modelcards.withgoogle.com/about` | `reports/canonical/experiment_stack_cards.json:$.cards[11]`, `reports/canonical/experiment_stack_cards.json:$.cards[12]` |
| `nist-ai-rmf` | `https://www.nist.gov/itl/ai-risk-management-framework` | `reports/canonical/experiment_stack_cards.json:$.cards[12]`, `reports/canonical/experiment_stack_cards.json:$.cards[13]` |

## Boundaries

- The card report is an auxiliary contract and does not promote model quality.
- Blocked card rows are owner gaps, not negative empirical evidence.
- Claim-first admission is delegated to the claim acceptance and consistency owners.
- External standard alignment is pointer-only and carries no independent certification.
