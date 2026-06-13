# Experiment Stack Cards

- Generated at: `2026-06-12T16:07:03.531460+00:00`
- Artifact: `bedc-quality-lab:experiment-stack-cards`
- Status: `blocked`
- Cards: `14`
- Claim-first gate: `reports/canonical/experiment_stack_cards.json:$.claim_first_gate`

## Cards

| card | status | owner issue | owner artifact | source | summary | demotion | hardgates |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `claim-card` | `blocked` | `child-of-1219:claim-card` | `reports/canonical/experiment_stack_claim_card.json` | `reports/canonical/experiment_stack_claim_card.json:$.claim_surface` | `reports/canonical/experiment_stack_claim_card.json:$.summary` | `reports/canonical/experiment_stack_claim_card.json:$.demotion_rule` | `STACK-HG1:fail, STACK-HG2:fail` |
| `task-target-card` | `blocked` | `child-of-1219:task-target-card` | `reports/canonical/experiment_stack_task_target_card.json` | `reports/canonical/experiment_stack_task_target_card.json:$.label_function` | `reports/canonical/experiment_stack_task_target_card.json:$.summary` | `reports/canonical/experiment_stack_task_target_card.json:$.demotion_rule` | `STACK-HG1:fail, STACK-HG2:fail` |
| `data-card` | `blocked` | `child-of-1219:data-card` | `reports/canonical/experiment_stack_data_card.json` | `reports/canonical/experiment_stack_data_card.json:$.data_boundary` | `reports/canonical/experiment_stack_data_card.json:$.summary` | `reports/canonical/experiment_stack_data_card.json:$.demotion_rule` | `STACK-HG1:fail, STACK-HG2:fail` |
| `feature-access-card` | `pass` | `1209` | `reports/canonical/dgt-l1-controls.json` | `reports/canonical/dgt-l1-controls.json:$.training_arms` | `reports/canonical/dgt-l1-controls.json:$.review_status` | `reports/canonical/dgt-l1-controls.json:$.l1_tiny_sequence_projection` | `STACK-HG1:pass, STACK-HG2:pass` |
| `baseline-validity-card` | `blocked` | `child-of-1219:baseline-validity-card` | `reports/canonical/experiment_stack_baseline_validity_card.json` | `reports/canonical/experiment_stack_baseline_validity_card.json:$.baseline_contract` | `reports/canonical/experiment_stack_baseline_validity_card.json:$.summary` | `reports/canonical/experiment_stack_baseline_validity_card.json:$.demotion_rule` | `STACK-HG1:fail, STACK-HG2:fail` |
| `ood-solvability-card` | `pass` | `1209,1203` | `reports/canonical/model-comparison.json` | `reports/canonical/model-comparison.json:$.models[0].metrics.ood_accuracy` | `reports/canonical/model-comparison.json:$.models[0].metrics_by_surface.out_of_distribution` | `reports/canonical/model-comparison.json:$.hardgates.MC-HG7` | `STACK-HG1:pass, STACK-HG2:pass` |
| `metric-provenance-card` | `pass` | `1201` | `reports/canonical/model-comparison.json` | `reports/canonical/model-comparison.json:$.models[0].metrics` | `reports/canonical/model-comparison.json:$.ranking_key` | `reports/canonical/model-comparison.json:$.hardgates.MC-HG3` | `STACK-HG1:pass, STACK-HG2:pass` |
| `training-authenticity-card` | `blocked` | `child-of-1219:training-authenticity-card` | `reports/canonical/experiment_stack_training_authenticity_card.json` | `reports/canonical/experiment_stack_training_authenticity_card.json:$.training_trace` | `reports/canonical/experiment_stack_training_authenticity_card.json:$.summary` | `reports/canonical/experiment_stack_training_authenticity_card.json:$.demotion_rule` | `STACK-HG1:fail, STACK-HG2:fail` |
| `statistical-evidence-card` | `blocked` | `child-of-1219:statistical-evidence-card` | `reports/canonical/experiment_stack_statistical_evidence_card.json` | `reports/canonical/experiment_stack_statistical_evidence_card.json:$.statistical_protocol` | `reports/canonical/experiment_stack_statistical_evidence_card.json:$.summary` | `reports/canonical/experiment_stack_statistical_evidence_card.json:$.demotion_rule` | `STACK-HG1:fail, STACK-HG2:fail` |
| `ablation-causal-evidence-card` | `blocked` | `child-of-1219:ablation-causal-evidence-card` | `reports/canonical/experiment_stack_ablation_causal_evidence_card.json` | `reports/canonical/experiment_stack_ablation_causal_evidence_card.json:$.causal_evidence` | `reports/canonical/experiment_stack_ablation_causal_evidence_card.json:$.summary` | `reports/canonical/experiment_stack_ablation_causal_evidence_card.json:$.demotion_rule` | `STACK-HG1:fail, STACK-HG2:fail` |
| `artifact-reproducibility-card` | `pass` | `1213` | `reports/release_manifest_sidecar.json` | `reports/release_manifest_sidecar.json:$.required_pointers` | `reports/release_manifest_sidecar.json:$.release_bundle_status` | `reports/release_manifest_sidecar.json:$.revoke_if` | `STACK-HG1:pass, STACK-HG2:pass` |
| `model-card` | `pass` | `1220` | `reports/canonical/model_design_suite.json` | `reports/canonical/model_design_suite.json:$.rows` | `reports/canonical/model_design_suite.json:$.status` | `reports/canonical/model_design_suite.json:$.not_claimed` | `STACK-HG1:pass, STACK-HG2:pass` |
| `risk-scope-review-card` | `blocked` | `child-of-1219:risk-scope-review-card` | `reports/canonical/experiment_stack_risk_scope_review_card.json` | `reports/canonical/experiment_stack_risk_scope_review_card.json:$.scope_review` | `reports/canonical/experiment_stack_risk_scope_review_card.json:$.summary` | `reports/canonical/experiment_stack_risk_scope_review_card.json:$.demotion_rule` | `STACK-HG1:fail, STACK-HG2:fail` |
| `release-readiness-board` | `blocked` | `child-of-1219:release-readiness-board` | `reports/canonical/experiment_stack_release_readiness_board.json` | `reports/canonical/experiment_stack_release_readiness_board.json:$.release_board` | `reports/canonical/experiment_stack_release_readiness_board.json:$.summary` | `reports/canonical/experiment_stack_release_readiness_board.json:$.demotion_rule` | `STACK-HG1:fail, STACK-HG2:fail` |

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
- Claim-first gating only controls training-result promotion ordering.
- External standard alignment is pointer-only and carries no independent certification.
