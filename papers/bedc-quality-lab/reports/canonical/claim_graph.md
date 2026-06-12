# Claim Graph

- Generated at: `2026-06-12T18:02:37.923159+00:00`
- Status: `pointer-only`
- Nodes: `143`

| node | type | source | depends on |
| --- | --- | --- | --- |
| `raw:mixing-family-sweep` | `raw_evidence` | `reports/canonical/mixing-family-sweep.json:$.coverage_item.debt_item` |  |
| `projected:mixing-family-sweep` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[0]` | `raw:mixing-family-sweep` |
| `raw:anisotropic-ou-sweep` | `raw_evidence` | `reports/canonical/anisotropic-ou-sweep.json:$.transition_debt_by_grid` |  |
| `projected:anisotropic-ou-sweep` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[1]` | `raw:anisotropic-ou-sweep` |
| `raw:gap-head-on-h` | `raw_evidence` | `reports/canonical/gap-head-on-h.json:$.treatment_verdict.positive` |  |
| `projected:gap-head-on-h` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[2]` | `raw:gap-head-on-h` |
| `raw:gap-head-discovery` | `raw_evidence` | `reports/canonical/gap-head-discovery.json:$.positive_discovery` |  |
| `projected:gap-head-discovery` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[3]` | `raw:gap-head-discovery` |
| `raw:gap-head-ablation` | `raw_evidence` | `reports/canonical/negative_discovery_reports.json:$.rows[0]` |  |
| `projected:gap-head-ablation` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[4]` | `raw:gap-head-ablation` |
| `raw:irreducibility-report` | `raw_evidence` | `reports/canonical/irreducibility_report.json:$` |  |
| `projected:irreducibility-report` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[5]` | `raw:irreducibility-report` |
| `raw:ledger-aware-transformer` | `raw_evidence` | `reports/canonical/ledger-aware-transformer.json:$.aggregate_metrics.uer_reduction` |  |
| `projected:ledger-aware-transformer` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[6]` | `raw:ledger-aware-transformer` |
| `raw:certificate-gated-attention` | `raw_evidence` | `reports/canonical/certificate-gated-attention.json:$.certificate_gate_summary.gated_vs_plain_valid` |  |
| `projected:certificate-gated-attention` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[7]` | `raw:certificate-gated-attention` |
| `raw:gap-head-threshold-frontier` | `raw_evidence` | `reports/canonical/gap-head-threshold-frontier.json:$` |  |
| `projected:gap-head-threshold-frontier` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[8]` | `raw:gap-head-threshold-frontier` |
| `raw:gap-head-transfer-atlas` | `raw_evidence` | `reports/canonical/gap_head_transfer_atlas.json:$.multi_surface_d5_o.decision` |  |
| `projected:gap-head-transfer-atlas` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[9]` | `raw:gap-head-transfer-atlas` |
| `raw:gap-head-attribution-capsule` | `raw_evidence` | `reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence` |  |
| `projected:gap-head-attribution-capsule` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[10]` | `raw:gap-head-attribution-capsule` |
| `raw:nongaussian-distribution-sweep` | `raw_evidence` | `reports/canonical/nongaussian-distribution-sweep.json:$.negative_result_ledger` |  |
| `projected:nongaussian-distribution-sweep` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[11]` | `raw:nongaussian-distribution-sweep` |
| `raw:certificate-guided-training` | `raw_evidence` | `reports/canonical/certificate-guided-training.json:$.arm_protocol.compat_roles.after` |  |
| `projected:certificate-guided-training` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[12]` | `raw:certificate-guided-training` |
| `raw:certificate-guided-discovery` | `raw_evidence` | `reports/canonical/negative_discovery_reports.json:$.rows[2]` |  |
| `projected:certificate-guided-discovery` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[13]` | `raw:certificate-guided-discovery` |
| `raw:sigreg-training-proxy` | `raw_evidence` | `reports/canonical/sigreg-training-proxy.json:$.d1_evidence.debt_delta` |  |
| `projected:sigreg-training-proxy` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[14]` | `raw:sigreg-training-proxy` |
| `raw:sigreg-mini-grid` | `raw_evidence` | `reports/canonical/sigreg-mini-grid.json:$.trend_summary.expected_trend` |  |
| `projected:sigreg-mini-grid` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[15]` | `raw:sigreg-mini-grid` |
| `raw:discovery-regularized-training` | `raw_evidence` | `reports/canonical/discovery-regularized-training.json:$.training_mechanism_cert` |  |
| `projected:discovery-regularized-training` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[16]` | `raw:discovery-regularized-training` |
| `raw:mechanism-seeking-network` | `raw_evidence` | `reports/canonical/mechanism-seeking-network.json:$.mechanism_gate_summary` |  |
| `projected:mechanism-seeking-network` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[17]` | `raw:mechanism-seeking-network` |
| `raw:mechanism-dna` | `raw_evidence` | `reports/canonical/mechanism_dna.json:$` |  |
| `projected:mechanism-dna` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[18]` | `raw:mechanism-dna` |
| `raw:dgt-l0-controls` | `raw_evidence` | `reports/canonical/dgt-l0-controls.json:$` |  |
| `projected:dgt-l0-controls` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[19]` | `raw:dgt-l0-controls` |
| `raw:winnability-certificates` | `raw_evidence` | `reports/canonical/winnability-certificates.json:$` |  |
| `projected:winnability-certificates` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[20]` | `raw:winnability-certificates` |
| `raw:structural-generalization-splits` | `raw_evidence` | `reports/canonical/structural-generalization-splits.json:$` |  |
| `projected:structural-generalization-splits` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[21]` | `raw:structural-generalization-splits` |
| `raw:dgt-base-undertraining-audit` | `raw_evidence` | `reports/canonical/dgt-base-undertraining-audit.json:$` |  |
| `projected:dgt-base-undertraining-audit` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[22]` | `raw:dgt-base-undertraining-audit` |
| `raw:input-accessibility` | `raw_evidence` | `reports/canonical/input-accessibility.json:$` |  |
| `projected:input-accessibility` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[23]` | `raw:input-accessibility` |
| `raw:fair-l1-decision` | `raw_evidence` | `reports/canonical/fair-l1-decision.json:$` |  |
| `projected:fair-l1-decision` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[24]` | `raw:fair-l1-decision` |
| `raw:discovery-gated-transformer` | `raw_evidence` | `reports/canonical/scaling-ladder.json:$.levels[0]` |  |
| `projected:discovery-gated-transformer` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[25]` | `raw:discovery-gated-transformer` |
| `raw:dgt-neural-ablation` | `raw_evidence` | `reports/canonical/dgt-neural-ablation.json:$.component_causal_claims` |  |
| `projected:dgt-neural-ablation` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[26]` | `raw:dgt-neural-ablation` |
| `raw:dgt-ablation-null-decomposition` | `raw_evidence` | `reports/canonical/dgt-ablation-null-decomposition.json:$` |  |
| `projected:dgt-ablation-null-decomposition` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[27]` | `raw:dgt-ablation-null-decomposition` |
| `raw:dgt-component-redundancy-audit` | `raw_evidence` | `reports/canonical/dgt-component-redundancy-audit.json:$` |  |
| `projected:dgt-component-redundancy-audit` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[28]` | `raw:dgt-component-redundancy-audit` |
| `raw:dgt-model-card` | `raw_evidence` | `reports/canonical/dgt-model-card.json:$` |  |
| `projected:dgt-model-card` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[29]` | `raw:dgt-model-card` |
| `raw:order-k-benchmark` | `raw_evidence` | `reports/canonical/order-k-benchmark.json:$` |  |
| `projected:order-k-benchmark` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[30]` | `raw:order-k-benchmark` |
| `raw:lejepa-theorem-ledger` | `raw_evidence` | `reports/canonical/lejepa_theorem_ledger.json:$.theorem_rows` |  |
| `projected:lejepa-theorem-ledger` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[31]` | `raw:lejepa-theorem-ledger` |
| `raw:observed-debt-sweep` | `raw_evidence` | `reports/canonical/observed-debt-sweep.json:$` |  |
| `projected:observed-debt-sweep` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[32]` | `raw:observed-debt-sweep` |
| `raw:spectral-ablation-hinge` | `raw_evidence` | `reports/canonical/negative_discovery_reports.json:$.rows[3]` |  |
| `projected:spectral-ablation-hinge` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[33]` | `raw:spectral-ablation-hinge` |
| `raw:model-comparison` | `raw_evidence` | `reports/canonical/model-comparison.json:$` |  |
| `projected:model-comparison` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[34]` | `raw:model-comparison` |
| `raw:causal-patch-suite` | `raw_evidence` | `reports/canonical/causal_patch_suite.json:$` |  |
| `projected:causal-patch-suite` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[35]` | `raw:causal-patch-suite` |
| `raw:experiment-stack-cards` | `raw_evidence` | `reports/canonical/experiment_stack_cards.json:$` |  |
| `projected:experiment-stack-cards` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[36]` | `raw:experiment-stack-cards` |
| `raw:dimension-mismatch-debt-transfer` | `raw_evidence` | `reports/canonical/dimension-mismatch-debt-transfer.json:$.dimension_mismatch_debt_transfer.effective_level` |  |
| `projected:dimension-mismatch-debt-transfer` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[37]` | `raw:dimension-mismatch-debt-transfer` |
| `raw:single-threshold-escape` | `raw_evidence` | `runs/single_threshold_escape_witness.json:$.single_threshold_basis` |  |
| `projected:single-threshold-escape` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[38]` | `raw:single-threshold-escape` |
| `raw:training-choice-observability` | `raw_evidence` | `runs/training_choice_observability.json:$.boundary_ledger` |  |
| `projected:training-choice-observability` | `projected_discovery` | `reports/canonical/discovery_map.json:$.rows[39]` | `raw:training-choice-observability` |
| `negative-witness:classifier_surface_delta_zero` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[0]` |  |
| `negative-witness:matched_control_positive` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[1]` |  |
| `negative-witness:hidden_debt_positive` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[2]` |  |
| `negative-witness:cost_protocol_missing` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[3]` |  |
| `negative-witness:scorecard_not_ready` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[4]` |  |
| `negative-witness:forbidden_inference_column` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[5]` |  |
| `negative-witness:benefit_debt_tradeoff` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[6]` |  |
| `negative-witness:fresh_claim_downgrade` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[7]` |  |
| `negative-witness:synthetic_leakage_injection` | `negative_witness` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[8]` |  |
| `revocation:witness:hidden_debt_positive` | `revocation` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[2]` | `negative-witness:hidden_debt_positive` |
| `revocation:witness:benefit_debt_tradeoff` | `revocation` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[6]` | `negative-witness:benefit_debt_tradeoff` |
| `revocation:witness:fresh_claim_downgrade` | `revocation` | `reports/canonical/discovery_negative_witnesses.json:$.witnesses[7]` | `negative-witness:fresh_claim_downgrade` |
| `mechanism:gap-head-attribution-capsule` | `mechanism_certificate` | `reports/canonical/gap_head_attribution_capsule.json:$.mechanism_evidence` |  |
| `mechanism:dgt-neural-ablation` | `mechanism_certificate` | `reports/canonical/dgt-neural-ablation.json:$.nabl_hardgates.status` |  |
| `terminal:mixing-family-sweep` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[0]` | `projected:mixing-family-sweep` |
| `terminal:anisotropic-ou-sweep` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[1]` | `projected:anisotropic-ou-sweep` |
| `terminal:gap-head-on-h` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[2]` | `projected:gap-head-on-h` |
| `terminal:gap-head-discovery` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[3]` | `projected:gap-head-discovery` |
| `terminal:gap-head-ablation` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[4]` | `projected:gap-head-ablation` |
| `terminal:irreducibility-report` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[5]` | `projected:irreducibility-report` |
| `terminal:ledger-aware-transformer` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[6]` | `projected:ledger-aware-transformer` |
| `terminal:certificate-gated-attention` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[7]` | `projected:certificate-gated-attention` |
| `terminal:gap-head-threshold-frontier` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[8]` | `projected:gap-head-threshold-frontier` |
| `terminal:gap-head-transfer-atlas` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[9]` | `projected:gap-head-transfer-atlas` |
| `terminal:gap-head-attribution-capsule` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[10]` | `projected:gap-head-attribution-capsule` |
| `terminal:nongaussian-distribution-sweep` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[11]` | `projected:nongaussian-distribution-sweep` |
| `terminal:certificate-guided-training` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[12]` | `projected:certificate-guided-training` |
| `terminal:certificate-guided-discovery` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[13]` | `projected:certificate-guided-discovery` |
| `terminal:sigreg-training-proxy` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[14]` | `projected:sigreg-training-proxy` |
| `terminal:sigreg-mini-grid` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[15]` | `projected:sigreg-mini-grid` |
| `terminal:discovery-regularized-training` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[16]` | `projected:discovery-regularized-training` |
| `terminal:mechanism-seeking-network` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[17]` | `projected:mechanism-seeking-network` |
| `terminal:mechanism-dna` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[18]` | `projected:mechanism-dna` |
| `terminal:dgt-l0-controls` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[19]` | `projected:dgt-l0-controls` |
| `terminal:winnability-certificates` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[20]` | `projected:winnability-certificates` |
| `terminal:structural-generalization-splits` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[21]` | `projected:structural-generalization-splits` |
| `terminal:dgt-base-undertraining-audit` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[22]` | `projected:dgt-base-undertraining-audit` |
| `terminal:input-accessibility` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[23]` | `projected:input-accessibility` |
| `terminal:fair-l1-decision` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[24]` | `projected:fair-l1-decision` |
| `terminal:discovery-gated-transformer` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[25]` | `projected:discovery-gated-transformer` |
| `terminal:dgt-neural-ablation` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[26]` | `projected:dgt-neural-ablation` |
| `terminal:dgt-ablation-null-decomposition` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[27]` | `projected:dgt-ablation-null-decomposition` |
| `terminal:dgt-component-redundancy-audit` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[28]` | `projected:dgt-component-redundancy-audit` |
| `terminal:dgt-model-card` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[29]` | `projected:dgt-model-card` |
| `terminal:order-k-benchmark` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[30]` | `projected:order-k-benchmark` |
| `terminal:lejepa-theorem-ledger` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[31]` | `projected:lejepa-theorem-ledger` |
| `terminal:observed-debt-sweep` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[32]` | `projected:observed-debt-sweep` |
| `terminal:spectral-ablation-hinge` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[33]` | `projected:spectral-ablation-hinge` |
| `terminal:model-comparison` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[34]` | `projected:model-comparison` |
| `terminal:causal-patch-suite` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[35]` | `projected:causal-patch-suite` |
| `terminal:experiment-stack-cards` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[36]` | `projected:experiment-stack-cards` |
| `terminal:dimension-mismatch-debt-transfer` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[37]` | `projected:dimension-mismatch-debt-transfer` |
| `terminal:single-threshold-escape` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[38]` | `projected:single-threshold-escape` |
| `terminal:training-choice-observability` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[39]` | `projected:training-choice-observability` |
| `terminal:witness:classifier_surface_delta_zero` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[40]` | `negative-witness:classifier_surface_delta_zero` |
| `terminal:witness:matched_control_positive` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[41]` | `negative-witness:matched_control_positive` |
| `terminal:witness:hidden_debt_positive` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[42]` | `revocation:witness:hidden_debt_positive` |
| `terminal:witness:cost_protocol_missing` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[43]` | `negative-witness:cost_protocol_missing` |
| `terminal:witness:scorecard_not_ready` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[44]` | `negative-witness:scorecard_not_ready` |
| `terminal:witness:forbidden_inference_column` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[45]` | `negative-witness:forbidden_inference_column` |
| `terminal:witness:benefit_debt_tradeoff` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[46]` | `revocation:witness:benefit_debt_tradeoff` |
| `terminal:witness:fresh_claim_downgrade` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[47]` | `revocation:witness:fresh_claim_downgrade` |
| `terminal:witness:synthetic_leakage_injection` | `terminal_claim` | `reports/canonical/claim_verdicts.jsonl:$.lines[48]` | `negative-witness:synthetic_leakage_injection` |

## Hardgates

- `CG-HG1`: `pass` accepted_positive_discovery terminals trace to raw_evidence through projected_discovery
- `CG-HG2`: `pass` D5 projected discoveries explicitly record whether a mechanism node exists
- `CG-HG3`: `pass` raw_evidence nodes are never terminal_claim nodes
- `CG-HG4`: `pass` claim verdict rows carry identity-only terminal graph foreign keys
- `CG-HG5`: `pass` all node source_pointer values resolve
- `CG-HG6`: `pass` accepted positive terminals have acceptance evidence bundle
- `CG-HG7`: `pass` nodes[*].depends_on forms an acyclic dependency graph; revocation nodes remain revocation evidence and are not positive forward-closure evidence
- `CG-HG8`: `pass` accepted high-impact terminal claims have resolvable review pointers
